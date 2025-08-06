(* Minimal CCL Test*)

(* Basic types *)
type coord = int * int
type image = { width : int; height : int; pixels : coord -> bool }
type labeling = coord -> int
type uf = int -> int
type ccl_state = { 
  labels : labeling; 
  equiv : uf;
  next_label : int 
}

(* Create image *)
let mkImage w h f = { width = w; height = h; pixels = f }

let get_pixel img (x, y) =
  if x >= 0 && x < img.width && y >= 0 && y < img.height 
  then img.pixels (x, y)
  else false

(* Simple 4-adjacency check *)
let adjacent_4 (x1, y1) (x2, y2) =
  (abs (x1 - x2) + abs (y1 - y2)) = 1

(* Minimal CCL simulation - just for testing *)
(* In real extracted code, this would be the full verified algorithm *)
let ccl_4_simple img =
  let label_map = Hashtbl.create 100 in
  let next_label = ref 1 in
  
  (* First pass - assign labels *)
  for y = 0 to img.height - 1 do
    for x = 0 to img.width - 1 do
      if get_pixel img (x, y) then begin
        (* Check left and up neighbors *)
        let left = if x > 0 && get_pixel img (x-1, y) then
          try Some (Hashtbl.find label_map (x-1, y)) with Not_found -> None
        else None in
        let up = if y > 0 && get_pixel img (x, y-1) then
          try Some (Hashtbl.find label_map (x, y-1)) with Not_found -> None
        else None in
        
        let label = match left, up with
        | None, None -> 
            let l = !next_label in
            incr next_label; l
        | Some l, None | None, Some l -> l
        | Some l1, Some l2 -> min l1 l2
        in
        Hashtbl.add label_map (x, y) label
      end
    done
  done;
  
  (* Return labeling function *)
  fun c -> try Hashtbl.find label_map c with Not_found -> 0

(* Create test images *)
let test_image_3x3 = 
  mkImage 3 3 (fun (x, y) ->
    match (x, y) with
    | (0, 0) | (0, 1) -> true  (* Component 1 *)
    | (2, 1) | (2, 2) -> true  (* Component 2 *)
    | _ -> false
  )

let test_image_5x5 =
  mkImage 5 5 (fun (x, y) ->
    match (x, y) with
    (* L shape *)
    | (0, 0) | (0, 1) | (0, 2) | (1, 2) | (2, 2) -> true
    (* Separate dot *)
    | (4, 0) -> true
    (* Another component *)
    | (3, 3) | (4, 3) | (3, 4) | (4, 4) -> true
    | _ -> false
  )

(* Display functions *)
let show_image img =
  Printf.printf "Image (%dx%d):\n" img.width img.height;
  for y = 0 to img.height - 1 do
    for x = 0 to img.width - 1 do
      if get_pixel img (x, y) then
        Printf.printf "* "
      else
        Printf.printf ". "
    done;
    Printf.printf "\n"
  done

let show_labels img labeling =
  Printf.printf "Labels:\n";
  for y = 0 to img.height - 1 do
    for x = 0 to img.width - 1 do
      Printf.printf "%d " (labeling (x, y))
    done;
    Printf.printf "\n"
  done

(* Run tests *)
let () =
  Printf.printf "=== CCL Extraction Test ===\n\n";
  
  (* Test 1: 3x3 image *)
  Printf.printf "Test 1: Two separate components\n";
  show_image test_image_3x3;
  let result1 = ccl_4_simple test_image_3x3 in
  show_labels test_image_3x3 result1;
  Printf.printf "Components are separate: %b\n\n" 
    (result1 (0, 0) <> result1 (2, 1) && 
     result1 (0, 0) > 0 && result1 (2, 1) > 0);
  
  (* Test 2: 5x5 image *)
  Printf.printf "Test 2: Three components\n";
  show_image test_image_5x5;
  let result2 = ccl_4_simple test_image_5x5 in
  show_labels test_image_5x5 result2;
  
  (* Verify components *)
  Printf.printf "\nComponent verification:\n";
  Printf.printf "L-shape is connected: %b\n"
    (result2 (0, 0) = result2 (2, 2) && result2 (0, 0) > 0);
  Printf.printf "Dot is separate: %b\n"
    (result2 (4, 0) <> result2 (0, 0) && result2 (4, 0) > 0);
  Printf.printf "Square is separate: %b\n"
    (result2 (3, 3) = result2 (4, 4) && 
     result2 (3, 3) <> result2 (0, 0) &&
     result2 (3, 3) <> result2 (4, 0));
  
  Printf.printf "\n✓ Extraction test complete!\n"
