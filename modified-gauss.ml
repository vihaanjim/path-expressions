open BatBitSet

type pathexp =
  (* ID, init, fin, vertices, expression*)
  int * int * int * BatBitSet.t * regex
and regex = 
  | Zero
  | One
  | Letter of int * int
  | Plus of pathexp * pathexp
  | Times of pathexp * pathexp
  | Star of pathexp

let nonzero = function
  | (_, _, _, _, Zero) -> false
  | _ -> true

let nonstar = function
  | (_, _, _, _, Star _) -> false
  | _ -> true

let id    (i, _, _, _, _) = i
let init  (_, i, _, _, _) = i
let fin   (_, _, f, _, _) = f
let verts (_, _, _, v, _) = v
let exp   (_, _, _, _, e) = e

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
  Printf.sprintf "%s#[%d-%d]" (to_string_ p 0) (init p) (fin p)

(* if they collide, one such vertex, otherwise none *)
let collides ?(besides = None) p1 p2 =
  let inter =
    BatBitSet.inter (verts p1) (verts p2)
    |> BatBitSet.remove (fin p1)
  in
  let inter = match besides with
    | Some v -> BatBitSet.remove v inter
    | None -> inter
  in
  BatBitSet.next_set_bit inter 0

let covers p u = BatBitSet.mem (verts p) u

(* simplification procedures *)
let empty_bitset = BatBitSet.create 30
let ops = ref 0

let zero i f = ops := !ops + 1 ; (!ops, i, f, empty_bitset, Zero)
let one i f = ops := !ops + 1 ; (!ops, i, f, empty_bitset, One)
let letter u v =
  ops := !ops + 1 ;
  let verts =
    empty_bitset |> BatBitSet.add u |> BatBitSet.add v
  in
  (!ops, u, v, verts, Letter (u, v))

let plus p1 p2 =
  ops := !ops + 1 ;
  if id p1 = id p2 then p1
  else 
    let i = init p1 and f = fin p1 in
    if i <> init p2 || f <> fin p2 then
      failwith (Printf.sprintf "Bad typing in union: %s and %s" (to_string p1) (to_string p2));
    match (exp p1, exp p2) with
    | (Zero, e2) -> p2
    | (e1, Zero) -> p1
    | _ ->
       (!ops, i, f, BatBitSet.union (verts p1) (verts p2), Plus (p1, p2))

let times ?(check = true) p1 p2 =
  ops := !ops + 1 ;
  let i = init p1 and m1 = fin p1
      and m2 = init p2 and f = fin p2
  in
  if m1 <> m2 then
    failwith (Printf.sprintf "Bad typing in concatenation: %s and %s" (to_string p1) (to_string p2)) ;
  match (exp p1, exp p2) with
  | (Zero, _) -> zero i f
  | (_, Zero) -> zero i f
  | (One, e2) -> p2
  | (e1, One) -> p1
  | _ ->
     if check && (
       (* two stars! *)
       (i = m1 && f = m2) 
       (* should be starred *)
       || (i = m1 && nonstar p1) 
       || (f = m2 && nonstar p2)
       (* collision *)
       || (i <> m1 && f <> m2 && i <> f && collides p1 p2 <> None)
       || (i = f && collides p1 p2 ~besides:(Some i) <> None)
     )
     then
       failwith (Printf.sprintf "Bad concat: %s and %s" (to_string p1) (to_string p2)) ;
     (!ops, i, f, BatBitSet.union (verts p1) (verts p2), Times (p1, p2))

let star p =
  ops := !ops + 1 ;
  let i = init p and f = fin p in
  if i <> f then
    failwith (Printf.sprintf "Bad typing in star: %s" (to_string p)) ;
  match exp p with 
  | Zero -> one i f
  | One -> one i f
  | _ -> (!ops, i, f, empty_bitset, Star p)

(* Gaussian elimination *)
let gauss ?(well_formed = true) n graph =
  let size = n + 1 in
  let paths = Array.init_matrix size size (fun u v -> zero u v) in
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
    else if Hashtbl.mem split_memo (u, id p) then
      Hashtbl.find split_memo (u, id p)
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
           (* the order matters here if the point of
              concatenation is u *)
           if covers p2 u then
             let (l2, r2, b2) = split u p2 in
             (times p1 l2, r2, times p1 b2)
           else
             let (l1, r1, b1) = split u p1 in
             (l1, times r1 p2, times b1 p2)
        | _ -> (zero i u, zero u f, p)
      in
      Hashtbl.add split_memo (u, id p) res ;
      res
  in
  let rec concat_well_formed p1 p2 =
    if not well_formed then times ~check:false p1 p2
    else 
      let besides =
        if init p1 = fin p2 then Some (init p1)
        else None
      in
      match collides ~besides:besides p1 p2 with
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

(* TESTING: count subexpressions. Very slow (exponential) *)
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
  Printf.printf "n\tNormal\tModified\n" ;
  flush stdout;
  for i = 2 to n do
    ops := 0 ;
    complete i |> gauss ~well_formed:false i ;
    let normal = !ops in
    ops := 0 ;
    complete i |> gauss i ;
    let modified = !ops in
    Printf.printf "%d\t%d\t%d\n" i normal modified ;
    flush stdout ;
  done
