open BatBitSet

type side = Entry | Exit
type augmented_vertex = int * side

let to_int = function
  | (u, Entry) -> 2 * u
  | (u, Exit)  -> 2 * u + 1
let to_augmented_vertex x =
  if x mod 2 = 0 then (x / 2, Entry)
  else (x / 2, Exit)

type pathexp =
  augmented_vertex * augmented_vertex * BatBitSet.t * regex
and regex = 
  | Zero
  | One
  | Letter of int * int
  | Plus of pathexp * pathexp
  | Times of pathexp * pathexp
  | Star of pathexp

let nonzero = function
  | (_, _, _, Zero) -> false
  | _ -> true

let init  (i, _, _, _) = i
let fin   (_, f, _, _) = f
let verts (_, _, v, _) = v
let exp   (_, _, _, e) = e

(* create nice string representation *)
(* I made DeepSeek create this. I have modified slightly. *)
let to_string p =
  let rec to_string_ p parent_prec =
    let (prec, s) = match exp p with
      | Zero -> (3, "0")
      | One  -> (3, "1")
      | Letter (h, t) -> (3, Printf.sprintf "‹%d, %d›" h t)
      | Plus (p1, p2) ->
         (0, (to_string_ p1 0) ^ " + " ^ (to_string_ p2 0))
      | Times (p1, p2) ->
         (1, (to_string_ p1 1) ^ (to_string_ p2 1))
      | Star p -> (2, (to_string_ p 2) ^ "*")
    in
    if prec < parent_prec then "(" ^ s ^ ")" else s
  in
  let aug_to_string = function
    | (u, Entry) -> Printf.sprintf "%d⊥" u
    | (u, Exit)  -> Printf.sprintf "%d⊤" u
  in
  Printf.sprintf "%s#[%s-%s]"
    (to_string_ p 0)
    (aug_to_string (init p))
    (aug_to_string (fin p))

(* if they collide, one such vertex, otherwise none *)
let collides p1 p2 =
  let inter =
    BatBitSet.inter (verts p1) (verts p2)
    |> BatBitSet.remove (to_int (fin p1))
  in
  BatBitSet.next_set_bit inter 0
  |> Option.map to_augmented_vertex

let covers p u = BatBitSet.mem (verts p) (to_int u)

(* simplification procedures *)
let empty_bitset = BatBitSet.create 50
let ops = ref 0

let zero i f = ops := !ops + 1 ; (i, f, empty_bitset, Zero)
let one i f = ops := !ops + 1 ; (i, f, empty_bitset, One)
let letter u v =
  ops := !ops + 1 ;
  let i = (u, Exit) and f = (v, Entry) in
  let verts =
    empty_bitset
    |> BatBitSet.add (to_int i) |> BatBitSet.add (to_int f)
  in
  (i, f, verts, Letter (u, v))

let plus_ops = ref 0
let plus p1 p2 =
  ops := !ops + 1 ;
  plus_ops := !plus_ops + 1;
  let i = init p1 and f = fin p1 in
  if i <> init p2 || f <> fin p2 then
    failwith (Printf.sprintf "Bad typing in union: %s and %s" (to_string p1) (to_string p2));
  match (exp p1, exp p2) with
  | (Zero, e2) -> p2
  | (e1, Zero) -> p1
  | _ ->
     (i, f, BatBitSet.union (verts p1) (verts p2), Plus (p1, p2))

let times_ops = ref 0
let times p1 p2 =
  ops := !ops + 1 ;
  times_ops := !times_ops + 1 ;
  let i = init p1 and (u1, s1) = fin p1
      and (u2, s2) = init p2 and f = fin p2
  in
  if u1 <> u2 || (s1 = Exit && s2 = Entry) then
    failwith (Printf.sprintf "Bad typing in concatenation: %s and %s" (to_string p1) (to_string p2)) ;
  match (exp p1, exp p2) with
  | (Zero, _) -> zero i f
  | (_, Zero) -> zero i f
  | (One, e2) -> (i, f, verts p2, exp p2)
  | (e1, One) -> (i, f, verts p1, exp p1)
  | _ ->
     if collides p1 p2 <> None then
       failwith (Printf.sprintf "Bad concat: %s and %s" (to_string p1) (to_string p2)) ;
     (i, f, BatBitSet.union (verts p1) (verts p2), Times (p1, p2))

let star p =
  ops := !ops + 1 ;
  let (u1, s1) = init p and (u2, s2) = fin p in
  if u1 <> u2 || s1 <> Exit || s2 <> Entry then
    failwith (Printf.sprintf "Bad typing in star: %s" (to_string p)) ;
  let i = (u1, Entry) and f = (u2, Exit) in
  match exp p with 
  | Zero -> one i f
  | One -> one i f
  | _ -> (i, f, empty_bitset, Star p)

(* Gaussian elimination *)
let gauss n graph =
  let size = n + 1 in
  let paths = Array.init_matrix size size
                (fun u v -> zero (u, Exit) (v, Entry)) in
  (* Suppose p has type <v, w>. Then, split u p returns (l, r, b)
     where l has type <v, u>, r has type <u, w>, no path
     recognized by b passes through u (unless it passes through a
     star), and p is equivalent to lr + b. We assume that p is
     well-formed. *)
  let split_memo = Hashtbl.create (size * size) in
  let rec split u p =
    let i = init p and f = fin p in
    if i = u then (one i i, p, zero i f)
    else if f = u then (p, one f f, zero i f)
    else if not (covers p u) then
      (zero i u, zero u f, p)
    else if Hashtbl.mem split_memo (u, p) then
      Hashtbl.find split_memo (u, p)
    else
      let res = 
        match exp p with 
        | Plus (p1, p2) ->
           let (l1, r1, b1) = split u p1 in
           let (l2, r2, b2) = split u p2 in
           (plus l1 l2,
            plus r1 r2,
            plus b1 b2)
        | Times (p1, p2) ->
           if covers p1 u then 
             let (l1, r1, b1) = split u p1 in
             (l1, times r1 p2, times b1 p2)
           else
             let (l2, r2, b2) = split u p2 in
             (times p1 l2, r2, times p1 b2)
        | _ -> (zero i u, zero u f, p)
      in
      Hashtbl.add split_memo (u, p) res ;
      res
  in
  let rec concat_well_formed p1 p2 =
    match collides p1 p2 with
    | Some x ->
       let (l1, r1, b1) = split x p1 in
       let (l2, r2, b2) = split x p2 in
       plus
         (times l1 (times (star (times r1 l2)) r2))
         (concat_well_formed b1 b2)
    | _ -> times p1 p2
  in
  (* add edges *)
  List.iteri
    (fun u out ->
      List.iter
        (fun v ->
          paths.(u).(v) <- plus paths.(u).(v) (letter u v))
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
  let rec count_ p =
    if not (Hashtbl.mem seen p) then
      Hashtbl.add seen p () ;
      match exp p with 
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
  Printf.printf "Processing to n=%d... may take a while\n" n ;
  Printf.printf "\tops\t(+)\t(.)\texprs\n" ;
  flush stdout;
  for i = 2 to n do
    ops := 0 ; plus_ops := 0 ; times_ops := 0 ;
    complete i |> gauss i |> Array.map count
    |> Array.fold_left Int.max 0 (* find max *)
    |> Printf.printf "n=%d:\t%d\t%d\t%d\t%d\n" i !ops !plus_ops !times_ops ;
    flush stdout ;
  done
