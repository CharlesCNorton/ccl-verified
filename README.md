# Formally Verified Connected Component Labeling in Rocq/Coq

A machine-checked proof that connected component labeling (CCL) is correct, for
binary images of arbitrary size, under both 4- and 8-connectivity. The
development is a single file with no axioms and no admitted goals, and it
extracts to executable OCaml.

CCL assigns a label to every pixel so that two foreground pixels share a label
exactly when they belong to the same connected region. It is a basic primitive
in medical imaging, industrial inspection, document analysis, and robotics.

## What is proved

The specification `correct_labeling img adj l` bundles four properties of a
labeling `l`:

- background pixels receive label 0;
- foreground pixels receive a positive label;
- connected pixels receive the same label (soundness);
- pixels with the same positive label are connected (completeness).

Both algorithms satisfy this specification in full, for both connectivities:

```coq
Theorem ccl_4_correct : forall img, correct_labeling img adjacent_4 (ccl_4 img).
Theorem ccl_8_correct : forall img, correct_labeling img adjacent_8 (ccl_8 img).
```

Because both directions are proved, sharing a label is equivalent to
connectivity on the foreground:

```coq
Theorem ccl_4_label_iff_connected : forall img c1 c2,
  get_pixel img c1 = true ->
  (ccl_4 img c1 = ccl_4 img c2 <-> connected img adjacent_4 c1 c2).
```

The labels are also compact: every value in `1..k`, with `k` the number of
components, is realized by some pixel (`ccl_4_label_onto`, `ccl_8_label_onto`),
and no label exceeds the number of components (`ccl_4_label_le_components`).

Every result is closed under the global context. `Print Assumptions` on the
correctness theorems reports no axioms.

## The efficient union-find is wired in and verified

The reference algorithm threads an abstract union-find `uf = nat -> nat`, whose
`find` costs O(number of unions). The development also defines a concrete
union-by-rank forest `ufr` whose `find` follows parent pointers, with depth
bounded by rank rather than by the number of unions:

```coq
Lemma ufind_root : forall u n x, ufr_wf u n -> uroot u (ufind u n x) = true.
Lemma ufind_idempotent : forall u n x, ufr_wf u n -> ufind u n (ufind u n x) = ufind u n x.
Lemma uunion_connects : ...                  (* union merges the two classes *)
Lemma uunion_preserves_rankmono : ...         (* union by rank keeps the forest valid *)
```

This forest refines the abstract structure rather than sitting beside it. A
single `uunion` induces the same partition as the abstract `uf_union`, and the
forest-backed pass produces the identical equivalence relation as the reference
pass at every step:

```coq
Lemma ufr_refines_union : forall u m l, ufr_ok u -> forall x y,
  uf_same_set (uf_union (Root u) m l) x y
  = Nat.eqb (Root (uunion u (S (ufr_maxrank u)) m l) x)
            (Root (uunion u (S (ufr_maxrank u)) m l) y).
Lemma InvF_pass : forall img adj cn, InvF (ccl_pass img adj cn) (ccl_pass_f img adj cn).
```

On top of that, the efficient algorithms `ccl_4_fast` and `ccl_8_fast`, which run
on the forest, are proved to satisfy the same full specification:

```coq
Theorem ccl_4_fast_correct : forall img, correct_labeling img adjacent_4 (ccl_4_fast img).
Theorem ccl_8_fast_correct : forall img, correct_labeling img adjacent_8 (ccl_8_fast img).
```

The fast and reference labelings need not agree on the exact label values, since
they choose different class representatives, but they induce the same partition
of pixels into components, and each is independently correct.

## Building

Checked with Rocq 9.0 (`coqc`). The file uses the `Stdlib` library namespace,
which is available in Coq 8.21 / Rocq 9 or later.

The filename contains a hyphen, which is not a valid module identifier, so
compile an underscore-named copy:

```bash
cp CCL-verified.v CCL_verified.v
coqc CCL_verified.v
```

Compilation also extracts the development to OCaml (`ccl_faithful.ml` and
`ccl_faithful.mli`), with `nat` mapped to Zarith for unbounded arithmetic. The
extracted module exposes both the reference (`ccl_4`, `ccl_8`) and the efficient
(`ccl_4_fast`, `ccl_8_fast`) algorithms, along with the union-by-rank
primitives. To build the bundled demo, which runs the extracted algorithm
directly:

```bash
ocamlfind ocamlopt -package zarith -c ccl_faithful.mli
ocamlfind ocamlopt -package zarith -linkpkg ccl_faithful.ml ccl_test_demo.ml -o ccl_demo
./ccl_demo
```

## Repository layout

- `CCL-verified.v` — the complete development.
- `ccl_test_demo.ml` — a small OCaml driver that exercises the extracted
  algorithm and prints labeled images.

## Structure of `CCL-verified.v`

1. Foundations: coordinates, images, 4/8-adjacency, raster scan order, and
   prior-neighbour generators with soundness and completeness.
2. Abstract union-find and label compaction.
3. Specification: the inductive `connected` relation and `correct_labeling`.
4. Single-pass algorithm: `process_pixel`, `ccl_pass`, `ccl_4`, `ccl_8`.
5. Soundness: connected pixels receive equal labels (`connected_pixels_same_label`).
6. Completeness: equal positive labels imply connectivity (`ccl_4_complete`).
7. 8-connectivity, via a generic adjacency-compatibility bridge instantiated for
   both relations.
8. Label-range exactness.
9. The union-by-rank forest, its refinement of the abstract union-find, and the
   verified efficient algorithms `ccl_4_fast` / `ccl_8_fast`.
10. Worked examples and extraction to OCaml.

## License

MIT.

## Citation

```bibtex
@software{norton_ccl_verified,
  author = {Norton, Charles C.},
  title  = {Formally Verified Connected Component Labeling in {Rocq}/{Coq}},
  year   = {2025},
  url    = {https://github.com/CharlesCNorton/ccl-verified},
  note   = {Axiom-free; 4- and 8-connectivity proved sound and complete; verified
            union-by-rank variant}
}
```

## Significance

To our knowledge this is the first complete formal verification of connected
component labeling proving both soundness and completeness for 4- and
8-connectivity, with a verified efficient union-by-rank implementation, giving a
machine-checked guarantee for a primitive used in safety-critical vision
systems.
