open BatBitSet

type pathexp =
  BatBitSet.t * regex
and regex = 
  | Zero
  | One
  | Letter of int * int
  | Plus of pathexp * pathexp
  | Times of pathexp * pathexp
  | Star of pathexp


let nonzero = function
  | (_, Zero) -> false
  | _ -> true

(* create nice string representation *)
(* I made DeepSeek create this. I have modified slightly. *)
let to_string r =
  let rec to_string_ (_, r) parent_prec =
    let prec = match r with
      | Zero | One | Letter _ -> 3
      | Plus _ -> 0
      | Times _ -> 1
      | Star _ -> 2
    in
    let s = match r with
      | Zero -> "0"
      | One  -> "1"
      | Letter (h, t) -> Printf.sprintf "‹%d, %d›" h t
      | Plus (r1, r2) ->
         (to_string_ r1 0) ^ " + " ^ (to_string_ r2 0)
      | Times (r1, r2) -> (to_string_ r1 1) ^ (to_string_ r2 1)
      | Star r -> (to_string_ r 2) ^ "*"
    in
    if prec < parent_prec then "(" ^ s ^ ")" else s
  in
  to_string_ r 0

(* if they collide, one such vertex, otherwise none *)
let collides (v1, _) (v2, _) =
  let inter = BatBitSet.inter v1 v2 in
  BatBitSet.next_set_bit inter 0

(* simplification procedures *)
let empty_bitset = BatBitSet.create 50

let zero = (empty_bitset, Zero)
let one = (empty_bitset, One)
let letter (u, v) =
  let set =
    empty_bitset
    |> BatBitSet.add (2 * u + 1) |> BatBitSet.add (2 * v)
  in
  (set, Letter (u, v))

let plus p1 p2 =
  let (v1, e1) = p1 and (v2, e2) = p2 in
  match (e1, e2) with
  | (Zero, e2) -> (v2, e2)
  | (e1, Zero) -> (v1, e1)
  | _ -> (BatBitSet.union v1 v2, Plus (p1, p2))

let times p1 p2 =
  let (v1, e1) = p1 and (v2, e2) = p2 in
  match (e1, e2) with
  | (Zero, _) -> zero
  | (_, Zero) -> zero
  | (One, e2) -> (v2, e2)
  | (e1, One) -> (v1, e1)
  | _ ->
     if collides p1 p2 <> None then
       failwith ("Bad concat: " ^ (to_string p1) ^ " AND " ^ (to_string p2)) ;
     (BatBitSet.union v1 v2, Times (p1, p2))

let star p =
  match p with 
  | (_, Zero) -> one
  | (_, One) -> one
  | _ -> (empty_bitset, Star p) (* todo: ban repeats *)

(* Suppose p has type <v, w>. Then, split u p returns (l, r, b)
   where l has type <v, u>, r has type <u, w>, no path recognized
   by b passes through u (unless it passes through a star), and p
   is equivalent to lr + b. We assume that p is well-formed. *)
let rec split u p =
  let (vs, e) = p and u_vert = u / 2 in
  match ((BatBitSet.mem vs u), e) with 
  | true, Letter (v, w) ->
     if v = u_vert then (one, p, zero)
     else if w = u_vert then (p, one, zero)
     else (zero, zero, p)
  | true, Plus (p1, p2) ->
     let (l1, r1, b1) = split u p1 in
     let (l2, r2, b2) = split u p2 in
     (plus l1 l2, plus r1 r2, plus b1 b2)
  | true, Times (p1, p2) ->
     let (l1, r1, b1) = split u p1 in
     (* if l1 is non empty, then it was split. by well-formedness,
        p2 does not contain u (except possibly inside stars). *)
     if nonzero l1 then (l1, times r1 p2, times b1 p2)
     else
       let (l2, r2, b2) = split u p2 in
       (times p1 l2, r2, times p1 b2)
  | _ -> (zero, zero, p)

let rec concat_well_formed p1 p2 =
  match collides p1 p2 with
  | Some x ->
     let (l1, r1, b1) = split x p1 in
     let (l2, r2, b2) = split x p2 in
     plus
       (times l1 (times (star (times r1 l2)) r2))
       (concat_well_formed b1 b2)
  | _ -> times p1 p2

(* Gaussian elimination *)
let gauss n graph =
  let size = n + 1 in
  let paths = Array.make_matrix size size zero in
  (* add edges *)
  List.iteri
    (fun u out ->
      List.iter
        (fun v ->
          paths.(u).(v) <- plus paths.(u).(v) (letter (u, v)))
        out
    )
    graph ;
  (* main loop *)
  for v = 0 to n - 1 do
    for u = v + 1 to n do
      paths.(u).(v) <- times paths.(u).(v) (star paths.(v).(v)) ;
      for w = 0 to n do
        if w <> v && nonzero paths.(u).(v) && nonzero paths.(v).(w) then
          paths.(u).(w) <-
            plus paths.(u).(w)
              (concat_well_formed paths.(u).(v) paths.(v).(w)) ;
      done ;
    done
  done ;
  paths.(n)

(* create a graph where the root vertex (labelled n) points to
   every vertex in a complete subgraph of size n (there is a
   vertex 0) *)
(* I had DeepSeek make this. *)
let complete n =  
  let others = List.init n (fun i -> i) in
  let adj_others =
    List.init n (fun i -> List.filter (fun j -> j <> i) others)
  in
  adj_others @ [others]

(* TESTING: count subexpressions. *)
let count p =
  let seen = Hashtbl.create 1024 in
  let rec count_ (_, e) =
    if not (Hashtbl.mem seen e) then
      Hashtbl.add seen e () ;
      match e with 
      | Plus (p1, p2) ->
         count_ p1 ;
         count_ p2
      | Times (p1, p2) ->
         count_ p1 ;
         count_ p2 
      | Star p1 -> 
         count_ p1
      | _ -> ()
  in
  count_ p ;
  Hashtbl.length seen

let test_to n =
  for i = 2 to n do
    complete i |> gauss i |> Array.map count
    |> Array.fold_left Int.max 0 (* find max *)
    |> Printf.printf "n=%d: %d\n" i ;
    flush stdout
  done

let () =
  let n = 15 in
  Printf.printf "Processing to n=%d... may take a while\n" n ;
  flush stdout;
  test_to 15
