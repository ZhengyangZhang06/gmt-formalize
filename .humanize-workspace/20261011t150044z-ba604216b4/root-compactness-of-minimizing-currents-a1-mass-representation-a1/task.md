# Recursive Lean task

# Simon GMT, Chapter 7: Area Minimizing Currents

Prove `GMT.Ch07.main_theorem`, stated in the frozen contract `GMT/Ch07/Contract.lean`, by completing `GMT/Ch07/Submission.lean` (initially a byte copy of the contract). The statement is the conjunction of the chapter's headline results; `GMT/Ch07/README.md` maps each conjunct to the book.

Source: Leon Simon, *Introduction to Geometric Measure Theory* (2014), Chapter 7, printed pages 181–204. Read-only copies for workers: `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt` and `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/simon-gmt.pdf` (printed page = PDF page − 7).

The natural-language proofs already exist in the book: base every natural-language proof and decomposition on Simon's printed proof of the corresponding result (cite the item and the line range in the chapter text), filling in omitted details and correcting printed errata. Only depart from the book where its argument is wrong or incomplete, and say so explicitly.

The pinned `simongmt` package (`Poincare.SimonGMT.*`) contains an earlier kernel-checked partial formalization of the book; its proofs may be reused as library lemmas where they apply. Do not rely on its definitions that the chapter README marks as unfaithful. Toolchain Lean v4.35.0-rc3, Mathlib 25730c7c. Every definition used by the statement must stay byte-identical; only standard axioms are allowed.
