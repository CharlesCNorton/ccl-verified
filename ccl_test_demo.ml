(* Extracted CCL - Complete *)

(* Types *)
type coord = int * int
type image = { width : int; height : int; pixels : coord -> bool }
type labeling = coord -> int
type uf = int -> int
type ccl_state = { 
  labels : labeling; 
  equiv : uf;
  next_label : int 
}

(* Core *)
let coord_x (x, _) = x
let coord_y (_, y) = y
let coord_eqb c1 c2 = (c1 = c2)

let mkImage w h f = { width = w; height = h; pixels = f }

let get_pixel img (x, y) =
  if x >= 0 && x < img.width && y >= 0 && y < img.height 
  then img.pixels (x, y)
  else false

let in_bounds img (x, y) =
  x >= 0 && x < img.width && y >= 0 && y < img.height

(* Adjacency *)
let abs_diff a b = abs (a - b)

let adjacent_4 (x1, y1) (x2, y2) =
  (abs_diff x1 x2) + (abs_diff y1 y2) = 1

let adjacent_8 (x1, y1) (x2, y2) =
  let dx = abs_diff x1 x2 in
  let dy = abs_diff y1 y2 in
  dx <= 1 && dy <= 1 && not (dx = 0 && dy = 0)

(* Order *)
let raster_lt (x1, y1) (x2, y2) =
  y1 < y2 || (y1 = y2 && x1 < x2)

(* Prior neighbors *)
let prior_neighbors_4 (x, y) =
  let neighbors = [] in
  let neighbors = if x > 0 then (x-1, y) :: neighbors else neighbors in
  let neighbors = if y > 0 then (x, y-1) :: neighbors else neighbors in
  neighbors

let prior_neighbors_8 img (x, y) =
  let neighbors = [] in
  let neighbors = if x > 0 && y > 0 then (x-1, y-1) :: neighbors else neighbors in
  let neighbors = if y > 0 then (x, y-1) :: neighbors else neighbors in
  let neighbors = if x+1 < img.width && y > 0 then (x+1, y-1) :: neighbors else neighbors in
  let neighbors = if x > 0 then (x-1, y) :: neighbors else neighbors in
  neighbors

let check_prior_neighbors_4 img c =
  List.filter (fun c' -> 
    get_pixel img c' && adjacent_4 c' c
  ) (prior_neighbors_4 c)

let check_prior_neighbors_8 img c =
  List.filter (fun c' ->
    get_pixel img c' && adjacent_8 c' c
  ) (prior_neighbors_8 img c)

let all_coords img =
  let coords = ref [] in
  for y = img.height - 1 downto 0 do
    for x = img.width - 1 downto 0 do
      coords := (x, y) :: !coords
    done
  done;
  !coords

(* Union-Find *)
let uf_init = fun x -> x

let uf_find u x = u x

let uf_union u x y =
  let px = uf_find u x in
  let py = uf_find u y in
  fun z -> if px = uf_find u z then py else uf_find u z

let uf_same_set u x y = (uf_find u x = uf_find u y)

let record_adjacency u min_label l =
  if min_label <> 0 && l <> 0 && min_label <> l then
    uf_union u min_label l
  else u

let resolve_labels u l =
  fun c -> uf_find u (l c)

let empty_labeling = fun _ -> 0

let initial_state = {
  labels = empty_labeling;
  equiv = uf_init;
  next_label = 1
}

(* Process pixel *)
let process_pixel img adj check_neighbors s c =
  if get_pixel img c then
    let neighbors = check_neighbors img c in
    let neighbor_labels = List.map s.labels neighbors in
    let positive_labels = List.filter (fun l -> l <> 0) neighbor_labels in
    match positive_labels with
    | [] -> 
        { labels = (fun c' -> if coord_eqb c c' then s.next_label else s.labels c');
          equiv = s.equiv;
          next_label = s.next_label + 1 }
    | l :: rest ->
        let min_label = List.fold_left min l rest in
        let new_equiv = List.fold_left (fun u l' -> record_adjacency u min_label l') 
                                       s.equiv positive_labels in
        { labels = (fun c' -> if coord_eqb c c' then min_label else s.labels c');
          equiv = new_equiv;
          next_label = s.next_label }
  else s

(* CCL pass *)
let ccl_pass img adj check_neighbors =
  List.fold_left (process_pixel img adj check_neighbors) initial_state (all_coords img)

(* Label compaction *)
let build_label_map u max_label =
  let representatives = ref [] in
  for i = 1 to max_label do
    if uf_find u i = i then representatives := i :: !representatives
  done;
  let map = Hashtbl.create (List.length !representatives) in
  let compact = ref 1 in
  List.iter (fun r ->
    Hashtbl.add map r !compact;
    incr compact
  ) (List.rev !representatives);
  fun label ->
    if label = 0 then 0
    else try Hashtbl.find map (uf_find u label) with Not_found -> 0

let compact_labels u l max_label =
  let label_map = build_label_map u max_label in
  fun c -> label_map (l c)

(* Main algorithms *)
let ccl_algorithm img adj check_neighbors =
  let final_state = ccl_pass img adj check_neighbors in
  let max_label = final_state.next_label - 1 in
  compact_labels final_state.equiv 
                 (resolve_labels final_state.equiv final_state.labels) 
                 max_label

let ccl_4 img = ccl_algorithm img adjacent_4 check_prior_neighbors_4
let ccl_8 img = ccl_algorithm img adjacent_8 check_prior_neighbors_8

(* Display *)
let show_pixel img c = if get_pixel img c then "*" else "."

let show_row img y =
  let s = ref "" in
  for x = 0 to img.width - 1 do
    s := !s ^ show_pixel img (x, y) ^ " "
  done;
  !s

let show_original img =
  let s = ref "" in
  for y = 0 to img.height - 1 do
    s := !s ^ show_row img y ^ "\n"
  done;
  !s

let label_to_ascii = function
  | 0 -> "." | 1 -> "1" | 2 -> "2" | 3 -> "3" | 4 -> "4"
  | 5 -> "5" | 6 -> "6" | 7 -> "7" | 8 -> "8" | 9 -> "9"
  | _ -> "+"

let display_row img labeling y =
  let s = ref "" in
  for x = 0 to img.width - 1 do
    s := !s ^ label_to_ascii (labeling (x, y)) ^ " "
  done;
  !s

let display_image img labeling =
  let s = ref "" in
  for y = 0 to img.height - 1 do
    s := !s ^ display_row img labeling y ^ "\n"
  done;
  !s

(* Test *)
let () =
  let img = mkImage 5 5 (fun c ->
    match c with
    | (0,0) | (1,0) | (0,1) | (1,1) -> true
    | (3,0) | (4,0) | (3,1) | (4,1) -> true
    | (2,3) -> true
    | (1,4) | (2,4) | (3,4) -> true
    | _ -> false
  ) in
  
  print_string (show_original img);
  print_string "\n4-connectivity:\n";
  print_string (display_image img (ccl_4 img));
  print_string "\n8-connectivity:\n";
  print_string (display_image img (ccl_8 img))
