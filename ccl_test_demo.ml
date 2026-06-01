(* Extraction-driven demo for CCL-verified.

   This driver exercises the *verified* algorithm directly: it calls the OCaml
   that Coq extracts from the development (module [Ccl_faithful]), rather than a
   hand translation. The printed labelings match the in-Coq [Compute] results.

   Build (the hyphen in the filename is not a valid Coq module identifier, so
   compile an underscore copy):

     cp CCL-verified.v CCL_verified.v
     coqc CCL_verified.v                 (* emits ccl_faithful.ml and ccl_faithful.mli *)
     ocamlfind ocamlopt -package zarith -c ccl_faithful.mli
     ocamlfind ocamlopt -package zarith -linkpkg ccl_faithful.ml ccl_test_demo.ml -o ccl_demo
     ./ccl_demo
*)

let show (name : string) (img : Ccl_faithful.image)
         (cc : Ccl_faithful.image -> Ccl_faithful.labeling) : unit =
  print_string ("=== " ^ name ^ " ===\n");
  print_string (Ccl_faithful.display_image img (cc img) (Ccl_faithful.height img))

let () =
  print_string "example_image (original):\n";
  print_string (Ccl_faithful.show_original Ccl_faithful.example_image
                  (Ccl_faithful.height Ccl_faithful.example_image));
  show "example_image, 4-connectivity" Ccl_faithful.example_image Ccl_faithful.ccl_4;
  show "example_image, 8-connectivity" Ccl_faithful.example_image Ccl_faithful.ccl_8;
  show "capstone_image, 4-connectivity" Ccl_faithful.capstone_image Ccl_faithful.ccl_4
