# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1`
- Child DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1.multilinear_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Provenance (for information only; nothing below depends on it): this is step 3 of the proof supplied for the parent theorem iwl_sp_covectorEuclideanNorm_pullback_le, with all details filled in.

Sibling lemma used (one_slot_bound, iwl_sp_pn_sum_sq_comp_basis_le): for every continuous linear L : ℝ^P → ℝ^Q and every linear f : ℝ^Q → ℝ, Σ_{a : Fin P} f(L e_a)² ≤ ‖L‖²·Σ_{b : Fin Q} f(e′_b)².

Notation. Fix P, Q ∈ ℕ and L : Eucl P →L[ℝ] Eucl Q.
- e_a := EuclideanSpace.basisFun (Fin P) ℝ a and e′_b := EuclideanSpace.basisFun (Fin Q) ℝ b.
- For i : Fin j → Fin P, Le∘i := (k ↦ L e_{i(k)}); for i : Fin j → Fin Q, e′∘i := (k ↦ e′_{i(k)}).
- Fin.cons x w is the (j+1)-tuple with entry x at 0 and w(k) at k.succ.

We prove H(j) by induction on j, where H(j) says: for every multilinear map β : MultilinearMap ℝ (fun _ : Fin j => Eucl Q) ℝ,
  Σ_{i : Fin j → Fin P} β(Le∘i)² ≤ (‖L‖²)^j · Σ_{i : Fin j → Fin Q} β(e′∘i)².

1. (Base case j = 0.)
   - Fin 0 → Fin P and Fin 0 → Fin Q each have exactly one element, so each sum has exactly one term (Fintype.sum_unique).
   - Le∘i and e′∘i both lie in Fin 0 → ℝ^Q, which has only one element, so they are equal.
   - Hence both sides equal β(())², since (‖L‖²)⁰ = 1, and H(0) holds with equality.
2. (Inductive step: setup.) Assume H(j) and let β be (j+1)-multilinear.
   (a) Splitting sums. For n ∈ {P, Q}, the map (a, i′) ↦ Fin.cons a i′ is a bijection Fin n × (Fin j → Fin n) → (Fin (j+1) → Fin n) (Fin.consEquiv). So for every G : (Fin (j+1) → Fin n) → ℝ, Σ_i G(i) = Σ_{a : Fin n} Σ_{i′ : Fin j → Fin n} G(Fin.cons a i′) (Fintype.sum_equiv, Fintype.sum_prod_type).
   (b) Cons and composition. For every map h : Fin n → X, (k ↦ h((Fin.cons a i′)(k))) = Fin.cons (h(a)) (k ↦ h(i′(k))); check k = 0 and k = k′.succ (Fin.cases). In particular Le∘(Fin.cons a i′) = Fin.cons (L e_a) (Le∘i′) and e′∘(Fin.cons b i″) = Fin.cons e′_b (e′∘i″).
   (c) Slot functionals. For w : Fin j → ℝ^Q, f_w(y) := β(Fin.cons y w) is ℝ-linear in y ∈ ℝ^Q, by multilinearity of β in slot 0 (MultilinearMap.cons_add, MultilinearMap.cons_smul).
3. (H(j) for each a.) For a ∈ Fin P, let β_a := β.curryLeft (L e_a), the j-multilinear map v ↦ β(Fin.cons (L e_a) v) (MultilinearMap.curryLeft_apply). H(j) for β_a gives
   Σ_{i′ : Fin j → Fin P} β(Fin.cons (L e_a) (Le∘i′))² ≤ (‖L‖²)^j · Σ_{i″ : Fin j → Fin Q} β(Fin.cons (L e_a) (e′∘i″))² = (‖L‖²)^j · Σ_{i″} f_{e′∘i″}(L e_a)².
4. (Summing over a and exchanging sums.) By 2(a), 2(b) and step 3 (Finset.sum_le_sum, Finset.mul_sum, Finset.sum_comm):
   Σ_{i : Fin (j+1) → Fin P} β(Le∘i)² = Σ_a Σ_{i′} β(Fin.cons (L e_a) (Le∘i′))²
   ≤ Σ_a (‖L‖²)^j Σ_{i″} f_{e′∘i″}(L e_a)²
   = (‖L‖²)^j · Σ_{i″} Σ_a f_{e′∘i″}(L e_a)².
5. (One slot.) For each i″, one_slot_bound applied to L and the linear map f := f_{e′∘i″} gives
   Σ_a f_{e′∘i″}(L e_a)² ≤ ‖L‖²·Σ_{b : Fin Q} f_{e′∘i″}(e′_b)² = ‖L‖²·Σ_b β(Fin.cons e′_b (e′∘i″))².
   Since (‖L‖²)^j ≥ 0, multiplying by it and summing over i″ preserves the inequality, so
   Σ_{i : Fin (j+1) → Fin P} β(Le∘i)² ≤ (‖L‖²)^j · Σ_{i″} ‖L‖²·Σ_b β(Fin.cons e′_b (e′∘i″))².
6. (Reassembling.) Pull out ‖L‖², use (‖L‖²)^j·‖L‖² = (‖L‖²)^{j+1} (pow_succ), exchange the sums over i″ and b, then apply 2(b) and 2(a) with n = Q:
   (‖L‖²)^j · Σ_{i″} ‖L‖²·Σ_b β(Fin.cons e′_b (e′∘i″))² = (‖L‖²)^{j+1} · Σ_b Σ_{i″} β(e′∘(Fin.cons b i″))² = (‖L‖²)^{j+1} · Σ_{i : Fin (j+1) → Fin Q} β(e′∘i)².
   This is H(j+1).

By induction, H(j) holds for all j ∈ ℕ. As P, Q and L were arbitrary, this is the claim.
No restriction on P or Q is used. If P = 0 or Q = 0, the sums over Fin P or Fin Q in steps 4–6 are empty and every step holds verbatim. The base case holds for all P, Q, since Fin 0 → Fin n has exactly one element.
β need not be alternating, symmetric or continuous. ∎

## Key steps

1. Induct on j, generalizing over β. The base case j = 0 is an equality because Fin 0 → X is a singleton.
2. Split sums over Fin (j+1) → Fin n through Fin.cons (Fin.consEquiv), and push maps through Fin.cons.
3. For each a ∈ Fin P, apply the induction hypothesis to β.curryLeft (L e_a).
4. Exchange the finite sums and apply one_slot_bound to the linear functionals y ↦ β(Fin.cons y (e′∘i″)).
5. Recombine with (‖L‖²)^j·‖L‖² = (‖L‖²)^{j+1} and Fin.consEquiv over Fin Q to get H(j+1).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp project/GMT/Ch06/Contract.lean workspace GMT/Ch06/Contract.lean (identical); cmp project/GMT/Ch06/Submission.lean project/GMT/Ch06/Contract.lean (identical)`
- `rg -n 'covectorEuclideanNorm|abbrev Covector|def Covector|Covector ' simongmt/Poincare/SimonGMT/Chapter06/*.lean; sed -n 1,80p Mass.lean; sed -n 1,60p Forms.lean; sed -n 140,175p FormsDuality.lean`
- `python3 -I scan of dag.json lean_name/lean_statement for covector/pullback/norm/factorial/iwl_sp names (slicing_mb_wn_sq_sum_eq_factorial_mul, slicing_mb_wn_norm_sq_eq_onb_sum, smr_ci_norm_eq_sqrt_sum_coord_sq, fiw_ims_sc_covectorNorm_le_opNorm, cmb_rb_covectorEuclideanNorm_add_le) and collision check of iwl_sp_pn_* names`
- `rg -n 'range_inj|strictMono_unique' mathlib/Mathlib/Order mathlib/Mathlib/Data/Fin`
- `rg -n 'theorem monotone_sort|def sort ' mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `rg -n 'map_perm|map_eq_zero_of_not_injective|compContinuousLinearMap_apply|toMultilinearMap' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `rg -n 'def curryLeft|curryLeft_apply' mathlib/Mathlib/LinearAlgebra/Multilinear/Curry.lean; rg -n 'def consEquiv|theorem comp_cons' mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `rg -ln 'HilbertSchmidt|hilbertSchmidt' mathlib/Mathlib/Analysis/InnerProductSpace mathlib/Mathlib/LinearAlgebra (no match); rg -n factorial mathlib/Mathlib/LinearAlgebra/Alternating mathlib/Mathlib/Topology/Algebra/Module/Alternating`
- `rg -n 'theorem basisFun_apply' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `verifier gmt-compare.py contract_scope + lean_contract.validate_lean_statement -> /tmp/iwl-sp-pn-decomp/lean/Challenge_*.lean`
- `leanrun.sh (lean-4.35.0-rc3, LEAN_PATH = workspace .lake/build + lake-packages-25730c7c) on Probe0.lean, Challenge_*.lean, Child1.lean, Child2.lean, Child3.lean, Assembly.lean, EndToEnd.lean with #print axioms`
- `python3 -I /tmp/iwl-sp-pn-decomp/scripts/check_children.py (900 random numeric cases)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Hom/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/DomCoprod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Multilinear/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/tmp/iwl-sp-pn-decomp/lean/EndToEnd.lean`
- `/tmp/iwl-sp-pn-decomp/lean/Assembly.lean`

Snapshot and project state:
- The snapshot is project d8d46c95 with Mathlib 25730c7c.
- The snapshot Contract is byte-identical to the workspace Contract, and Submission is byte-identical to Contract, so no Submission.* declarations exist yet.
- Covector E n = E [⋀^Fin n]→L[ℝ] ℝ (Forms.lean:31). covectorEuclideanNorm (Mass.lean:30) is the square root of the sum over strictly increasing I of alpha(basisFun ∘ I)².

No existing lemma to reuse:
- No Mathlib lemma gives the pullback bound, a Hilbert–Schmidt estimate, or the factorial tuple identity. There is no HilbertSchmidt match, and the factorial hits under Alternating are only the unrelated alternatization and domCoprod identities. All three children must therefore be proved.

The Mathlib ingredients the children use all exist:
- Tuple.sort and Tuple.monotone_sort (Data/Fin/Tuple/Sort.lean:80, 95);
- StrictMono.range_inj_of_wellFoundedLT (Order/WellFounded.lean:249);
- ContinuousAlternatingMap.map_eq_zero_of_not_injective and compContinuousLinearMap_apply (Topology/Algebra/Module/Alternating/Basic.lean:137, 319);
- AlternatingMap.map_perm (LinearAlgebra/Alternating/Basic.lean:672);
- MultilinearMap.curryLeft_apply (LinearAlgebra/Multilinear/Curry.lean:85);
- Fin.consEquiv (Data/Fin/Tuple/Basic.lean:184);
- EuclideanSpace.basisFun_apply (PiL2.lean:806).

DAG:
- The names iwl_sp_pn_sum_sq_tuples_eq_factorial_mul, iwl_sp_pn_sum_sq_comp_basis_le and iwl_sp_pn_multilinear_sum_sq_le are free.
- slicing_mb_wn_sq_sum_eq_factorial_mul is related, but it has a different type and status rlcr-lean (not accepted), so it is not reused.

Scratch Lean checks (pinned lean-4.35.0-rc3):
- All three child types elaborate in the comparator child scope and pass validate_lean_statement.
- EndToEnd.lean proves the three children and the frozen parent from them, with no sorry and only the axioms propext, Classical.choice and Quot.sound.
- An independent reviewer re-ran these files and accepted the split.
