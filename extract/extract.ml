open Big_int;;
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  match b1 with
  | false ->
    (match b2 with
     | false -> true
     | true -> false)
  | true -> b2

(** val negb : bool -> bool **)

let negb = function
| false -> true
| true -> false

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,y -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| x,y -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

(** val pred : big_int -> big_int **)

let pred n =
  (fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
    (fun _ ->
    n)
    (fun u ->
    u)
    n

(** val plus : big_int -> big_int -> big_int **)

let rec plus = add_big_int

(** val mult : big_int -> big_int -> big_int **)

let rec mult = mult_big_int

(** val minus : big_int -> big_int -> big_int **)

let rec minus = sub_big_int

(** val even_odd_dec : big_int -> bool **)

let rec even_odd_dec = fun a -> not (eq_big_int zero_big_int (mod_big_int a (big_int_of_int 2)))

(** val div2 : big_int -> big_int **)

let rec div2 = fun a -> div_big_int a (big_int_of_int 2)

(** val double : big_int -> big_int **)

let double n =
  plus n n

(** val double_plus1 : big_int -> big_int **)

let double_plus1 n =
  succ_big_int (double n)

(** val even_oddb : big_int -> bool **)

let even_oddb n =
  match even_odd_dec n with
  | false -> false
  | true -> true

type 'a bin_tree =
| Bt_mt
| Bt_node of 'a * 'a bin_tree * 'a bin_tree

type 'a c = 'a

(** val ret : 'a1 -> 'a1 c **)

let ret a =
  a

(** val bind : 'a1 c -> ('a1 -> __ -> 'a2 c) -> 'a2 c **)

let bind am bf =
  bf am __

(** val inc : big_int -> 'a1 c -> 'a1 c **)

let inc k xc =
  xc

(** val insert : 'a1 -> 'a1 bin_tree -> 'a1 bin_tree c **)

let rec insert i = function
| Bt_mt -> Bt_node (i, Bt_mt, Bt_mt)
| Bt_node (j, s, t) -> Bt_node (i, (insert j t), s)

(** val copy_linear_func : (__*(__*big_int)) -> __ bin_tree c **)

let rec copy_linear_func x =
  let x0 = let a,p = let x0,h = x in h in a in
  let n = let x1,h = let x1,h = x in h in h in
  let copy_linear0 = fun x1 n0 -> let y = __,(x1,n0) in copy_linear_func y in
  ((fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
     (fun _ ->
     Bt_mt)
     (fun n' -> Bt_node (x0, (copy_linear0 x0 (div2 n)),
     (copy_linear0 x0 (div2 n'))))
     n)

(** val copy_linear : 'a1 -> big_int -> 'a1 bin_tree c **)

let copy_linear x n =
  Obj.magic (copy_linear_func (__,((Obj.magic x),n)))

(** val add1 : big_int -> big_int c **)

let rec add1 x =
  let add2 = fun n -> add1 n in
  ((fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
     (fun _ -> succ_big_int
     zero_big_int)
     (fun wildcard' ->
     match even_odd_dec x with
     | false -> plus x (succ_big_int zero_big_int)
     | true -> let sd2 = add2 (div2 x) in plus sd2 sd2)
     x)

(** val plus_cin_func : (big_int*(big_int*bool)) -> big_int c **)

let rec plus_cin_func x =
  let n = let a,p = x in a in
  let m = let a,p = let x0,h = x in h in a in
  let cin = let x0,h = let x0,h = x in h in h in
  let plus_cin0 = fun n0 m0 cin0 -> let y = n0,(m0,cin0) in plus_cin_func y
  in
  ((fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
     (fun _ ->
     (fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
       (fun _ ->
       match cin with
       | false -> succ_big_int zero_big_int
       | true -> zero_big_int)
       (fun m' ->
       match cin with
       | false -> add1 m
       | true -> m)
       m)
     (fun n' ->
     (fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
       (fun _ ->
       match cin with
       | false -> add1 n
       | true -> n)
       (fun m' ->
       let filtered_var = xorb (xorb (even_oddb n) (even_oddb m)) cin in
       (match filtered_var with
        | false ->
          double_plus1
            (plus_cin0 (div2 n) (div2 m)
              (match match negb (even_oddb n) with
                     | false -> negb (even_oddb m)
                     | true -> true with
               | false -> false
               | true ->
                 (match cin with
                  | false -> xorb (even_oddb n) (even_oddb m)
                  | true -> true)))
        | true ->
          double
            (plus_cin0 (div2 n) (div2 m)
              (match match negb (even_oddb n) with
                     | false -> negb (even_oddb m)
                     | true -> true with
               | false -> false
               | true ->
                 (match cin with
                  | false -> xorb (even_oddb n) (even_oddb m)
                  | true -> true)))))
       m)
     n)

(** val plus_cin : big_int -> big_int -> bool -> big_int c **)

let plus_cin n m cin =
  plus_cin_func (n,(m,cin))

(** val tplus : big_int -> big_int -> big_int c **)

let rec tplus n m =
  plus_cin n m true

(** val copy_fib_func : ('a1*big_int) -> 'a1 bin_tree c **)

let rec copy_fib_func x =
  let x0 = let a,p = x in a in
  let n = let x1,h = x in h in
  let copy_fib0 = fun x1 n0 -> let y = x1,n0 in copy_fib_func y in
  ((fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
     (fun _ ->
     Bt_mt)
     (fun n0 ->
     match even_odd_dec n with
     | false ->
       Bt_node (x0, (copy_fib0 x0 (div2 n)),
         (copy_fib0 x0 (minus (div2 n) (succ_big_int zero_big_int))))
     | true -> let t = copy_fib0 x0 (div2 n) in Bt_node (x0, t, t))
     n)

(** val copy_fib : 'a1 -> big_int -> 'a1 bin_tree c **)

let copy_fib x n =
  copy_fib_func (x,n)

(** val copy_log_sq_func : (__*(__*big_int)) -> __ bin_tree c **)

let rec copy_log_sq_func x =
  let x0 = let a,p = let x0,h = x in h in a in
  let n = let x1,h = let x1,h = x in h in h in
  let copy_log_sq0 = fun x1 n0 -> let y = __,(x1,n0) in copy_log_sq_func y in
  ((fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
     (fun _ ->
     Bt_mt)
     (fun n' ->
     let t = copy_log_sq0 x0 (div2 n') in
     (match even_odd_dec n' with
      | false -> Bt_node (x0, t, t)
      | true -> Bt_node (x0, (insert x0 t), t)))
     n)

(** val copy_log_sq : 'a1 -> big_int -> 'a1 bin_tree c **)

let copy_log_sq x n =
  Obj.magic (copy_log_sq_func (__,((Obj.magic x),n)))

(** val copy2_func : (__*(__*big_int)) -> (__ bin_tree*__ bin_tree) c **)

let rec copy2_func x =
  let x0 = let a,p = let x0,h = x in h in a in
  let n = let x1,h = let x1,h = x in h in h in
  let copy3 = fun x1 n0 -> let y = __,(x1,n0) in copy2_func y in
  ((fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
     (fun _ -> (Bt_node (x0, Bt_mt,
     Bt_mt)),Bt_mt)
     (fun n' ->
     let s,t = copy3 x0 (div2 n') in
     (match even_odd_dec n' with
      | false -> (Bt_node (x0, s, t)),(Bt_node (x0, t, t))
      | true -> (Bt_node (x0, s, s)),(Bt_node (x0, s, t))))
     n)

(** val copy2 : 'a1 -> big_int -> ('a1 bin_tree*'a1 bin_tree) c **)

let copy2 x n =
  Obj.magic (copy2_func (__,((Obj.magic x),n)))

(** val copy : 'a1 -> big_int -> 'a1 bin_tree c **)

let rec copy x n =
  let s,t = copy2 x n in t

(** val size_linear : 'a1 bin_tree -> big_int c **)

let rec size_linear = function
| Bt_mt -> zero_big_int
| Bt_node (x, l, r) ->
  plus (plus (size_linear l) (size_linear r)) (succ_big_int zero_big_int)

(** val diff_func : (__*(__ bin_tree*big_int)) -> big_int c **)

let rec diff_func x =
  let b = let a,p = let x0,h = x in h in a in
  let m = let x0,h = let x0,h = x in h in h in
  let diff0 = fun b0 m0 -> let y = __,(b0,m0) in diff_func y in
  (match b with
   | Bt_mt -> zero_big_int
   | Bt_node (x0, s, t) ->
     ((fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
        (fun _ -> succ_big_int
        zero_big_int)
        (fun m' ->
        match even_odd_dec m with
        | false -> diff0 t (div2 (minus m' (succ_big_int zero_big_int)))
        | true -> diff0 s (div2 m'))
        m))

(** val diff : 'a1 bin_tree -> big_int -> big_int c **)

let diff b m =
  diff_func (__,((Obj.magic b),m))

(** val size : 'a1 bin_tree -> big_int c **)

let rec size = function
| Bt_mt -> zero_big_int
| Bt_node (wildcard', s, t) ->
  let m = size t in
  plus
    (plus (succ_big_int zero_big_int)
      (mult (succ_big_int (succ_big_int zero_big_int)) m)) (diff s m)

(** val make_array_naive : 'a1 list -> 'a1 bin_tree c **)

let rec make_array_naive = function
| Nil -> Bt_mt
| Cons (x, xs') -> insert x (make_array_naive xs')

type ('a, 'b) f_type = 'a -> 'b -> 'b c

type ('a, 'b) base_type = 'b

(** val foldr :
    ('a1, 'a2) f_type -> ('a1, 'a2) base_type -> 'a1 list -> 'a2 c **)

let rec foldr f base = function
| Nil -> base
| Cons (x, xs) -> f x (foldr f base xs)

(** val make_array_naive0 : 'a1 list -> 'a1 bin_tree c **)

let make_array_naive0 l =
  foldr (fun x y -> insert x y) Bt_mt l

(** val unravel : 'a1 list -> ('a1 list*'a1 list) c **)

let rec unravel = function
| Nil -> Nil,Nil
| Cons (x, xs') -> let odds,evens = unravel xs' in (Cons (x, evens)),odds

(** val make_array_td_func : (__*__ list) -> __ bin_tree c **)

let rec make_array_td_func x =
  let xs = let x0,h = x in h in
  let make_array_td0 = fun xs0 -> let y = __,xs0 in make_array_td_func y in
  (match xs with
   | Nil -> Bt_mt
   | Cons (x0, xs') ->
     let odds,evens = unravel xs' in
     Bt_node (x0, (make_array_td0 odds), (make_array_td0 evens)))

(** val make_array_td : 'a1 list -> 'a1 bin_tree c **)

let make_array_td xs =
  Obj.magic (make_array_td_func (__,(Obj.magic xs)))

(** val cinterleave_func : (__*(__ list*__ list)) -> __ list c **)

let rec cinterleave_func x =
  let e = let a,p = let x0,h = x in h in a in
  let o = let x0,h = let x0,h = x in h in h in
  let cinterleave0 = fun e0 o0 -> let y = __,(e0,o0) in cinterleave_func y in
  (match e with
   | Nil -> o
   | Cons (x0, xs) -> Cons (x0, (cinterleave0 o xs)))

(** val cinterleave : 'a1 list -> 'a1 list -> 'a1 list c **)

let cinterleave e o =
  Obj.magic (cinterleave_func (__,((Obj.magic e),(Obj.magic o))))

(** val to_list_naive : 'a1 bin_tree -> 'a1 list c **)

let rec to_list_naive = function
| Bt_mt -> Nil
| Bt_node (x, s, t) ->
  Cons (x, (cinterleave (to_list_naive s) (to_list_naive t)))

(** val sub1 : big_int -> big_int c **)

let rec sub1 x =
  let sub2 = fun n -> sub1 n in
  ((fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
     (fun _ ->
     zero_big_int)
     (fun wildcard' ->
     match even_odd_dec x with
     | false ->
       let sd2 = sub2 (div2 x) in
       plus (plus sd2 sd2) (succ_big_int zero_big_int)
     | true -> minus x (succ_big_int zero_big_int))
     x)

type 'a decCmp = 'a -> 'a -> bool

(** val insert0 : 'a1 decCmp -> 'a1 -> 'a1 list -> 'a1 list c **)

let rec insert0 a_cmp_dec a l = match l with
| Nil -> Cons (a, Nil)
| Cons (a', l') ->
  let filtered_var = a_cmp_dec a a' in
  (match filtered_var with
   | false -> Cons (a, l)
   | true -> Cons (a', (insert0 a_cmp_dec a l')))

(** val isort : 'a1 decCmp -> 'a1 list -> 'a1 list c **)

let rec isort a_cmp_dec = function
| Nil -> Nil
| Cons (a, d) -> insert0 a_cmp_dec a (isort a_cmp_dec d)

(** val clength : 'a1 list -> big_int c **)

let rec clength = function
| Nil -> zero_big_int
| Cons (a', l') -> plus (clength l') (succ_big_int zero_big_int)

(** val split2_obligation_2 :
    big_int -> 'a1 list -> big_int -> 'a1 list*'a1 list **)

let split2_obligation_2 n l n' =
  assert false (* absurd case *)

(** val split2 : big_int -> 'a1 list -> ('a1 list*'a1 list) c **)

let rec split2 n l =
  (fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
    (fun _ ->
    Nil,l)
    (fun n' ->
    match l with
    | Nil -> split2_obligation_2 n l n'
    | Cons (a, l') ->
      let res = split2 n' l' in (Cons (a, (fst res))),(snd res))
    n

(** val merge_func :
    (__*(__*(__*(__*(__ decCmp*(__ list*__ list)))))) -> __ list c **)

let rec merge_func x =
  let a_cmp_dec =
    let a,p =
      let x0,h = let x0,h = let x0,h = let x0,h = x in h in h in h in h
    in
    a
  in
  let xs =
    let a,p =
      let x0,h =
        let x0,h = let x0,h = let x0,h = let x0,h = x in h in h in h in h
      in
      h
    in
    a
  in
  let ys =
    let x0,h =
      let x0,h =
        let x0,h = let x0,h = let x0,h = let x0,h = x in h in h in h in h
      in
      h
    in
    h
  in
  let merge0 = fun a_cmp_dec0 xs0 ys0 ->
    let y = __,(__,(__,(__,(a_cmp_dec0,(xs0,ys0))))) in merge_func y
  in
  (match xs with
   | Nil -> ys
   | Cons (x0, xs') ->
     (match ys with
      | Nil -> xs
      | Cons (y, ys') ->
        let filtered_var = a_cmp_dec x0 y in
        (match filtered_var with
         | false -> Cons (x0, (merge0 a_cmp_dec xs' ys))
         | true -> Cons (y, (merge0 a_cmp_dec xs ys')))))

(** val merge : 'a1 decCmp -> 'a1 list -> 'a1 list -> 'a1 list c **)

let merge a_cmp_dec xs ys =
  Obj.magic
    (merge_func
      (__,(__,(__,(__,((Obj.magic a_cmp_dec),((Obj.magic xs),(Obj.magic ys))))))))

(** val mergesortc_func :
    (__*(__*(__*(__*(__ decCmp*(__ list*(big_int*__))))))) -> __ list c **)

let rec mergesortc_func x =
  let a_cmp_dec =
    let a,p =
      let x0,h = let x0,h = let x0,h = let x0,h = x in h in h in h in h
    in
    a
  in
  let l =
    let a,p =
      let x0,h =
        let x0,h = let x0,h = let x0,h = let x0,h = x in h in h in h in h
      in
      h
    in
    a
  in
  let len =
    let a,p =
      let x0,h =
        let x0,h =
          let x0,h = let x0,h = let x0,h = let x0,h = x in h in h in h in h
        in
        h
      in
      h
    in
    a
  in
  let mergesortc0 = fun a_cmp_dec0 l0 len0 ->
    let y = __,(__,(__,(__,(a_cmp_dec0,(l0,(len0,__)))))) in
    mergesortc_func y
  in
  (match l with
   | Nil -> Nil
   | Cons (x0, l') ->
     (match even_odd_dec len with
      | false ->
        let xs12 = split2 (div2 len) l in
        merge a_cmp_dec (mergesortc0 a_cmp_dec (fst xs12) (div2 len))
          (mergesortc0 a_cmp_dec (snd xs12) (div2 len))
      | true -> insert0 a_cmp_dec x0 (mergesortc0 a_cmp_dec l' (pred len))))

(** val mergesortc : 'a1 decCmp -> 'a1 list -> big_int -> 'a1 list c **)

let mergesortc a_cmp_dec l len =
  Obj.magic
    (mergesortc_func
      (__,(__,(__,(__,((Obj.magic a_cmp_dec),((Obj.magic l),(len,__))))))))

(** val mergesort : 'a1 decCmp -> 'a1 list -> 'a1 list c **)

let rec mergesort a_cmp_dec l =
  mergesortc a_cmp_dec l (clength l)

(** val fib_iter_loop :
    big_int -> big_int -> big_int -> big_int -> big_int c **)

let rec fib_iter_loop fuel target a b =
  (fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
    (fun _ ->
    b)
    (fun fuel0 ->
    fib_iter_loop fuel0 target b (tplus a b))
    fuel

(** val fib_iter : big_int -> big_int c **)

let rec fib_iter target =
  (fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
    (fun _ ->
    zero_big_int)
    (fun target' ->
    (fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
      (fun _ -> succ_big_int
      zero_big_int)
      (fun target'' ->
      fib_iter_loop target' target zero_big_int (succ_big_int zero_big_int))
      target')
    target

(** val fib_rec : big_int -> big_int c **)

let rec fib_rec n =
  (fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
    (fun _ ->
    zero_big_int)
    (fun n' ->
    (fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
      (fun _ -> succ_big_int
      zero_big_int)
      (fun n'' ->
      plus (fib_rec n'') (fib_rec n'))
      n')
    n

(** val insert_at_obligation_2 :
    'a1 -> big_int -> 'a1 list -> big_int -> 'a1 list **)

let insert_at_obligation_2 a n l np =
  assert false (* absurd case *)

(** val insert_at : 'a1 -> big_int -> 'a1 list -> 'a1 list c **)

let rec insert_at a n l =
  (fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
    (fun _ -> Cons (a,
    l))
    (fun np ->
    match l with
    | Nil -> insert_at_obligation_2 a n l np
    | Cons (ap, lp) -> Cons (ap, (insert_at a np lp)))
    n

(** val minsert_at : 'a1 list -> big_int -> 'a1 list -> 'a1 list c **)

let rec minsert_at ma n l =
  match ma with
  | Nil -> l
  | Cons (a, map) -> minsert_at map n (insert_at a n l)

type 'a zipper = 'a list*'a list

(** val to_zip : 'a1 list -> 'a1 zipper c **)

let rec to_zip l =
  Nil,l

(** val from_zip : 'a1 zipper -> 'a1 list c **)

let rec from_zip z =
  snd z

(** val zip_right_obligation_1 : 'a1 zipper -> 'a1 zipper **)

let zip_right_obligation_1 z =
  z

(** val zip_right : 'a1 zipper -> 'a1 zipper c **)

let rec zip_right z =
  let filtered_var = snd z in
  (match filtered_var with
   | Nil -> zip_right_obligation_1 z
   | Cons (a, ys) -> (Cons (a, (fst z))),ys)

(** val zip_left_obligation_1 : 'a1 zipper -> 'a1 zipper **)

let zip_left_obligation_1 z =
  z

(** val zip_left : 'a1 zipper -> 'a1 zipper c **)

let rec zip_left z =
  let filtered_var = fst z in
  (match filtered_var with
   | Nil -> zip_left_obligation_1 z
   | Cons (b, xs) -> xs,(Cons (b, (snd z))))

(** val zip_insert : 'a1 zipper -> 'a1 -> 'a1 zipper c **)

let rec zip_insert z a =
  (fst z),(Cons (a, (snd z)))

(** val zip_rightn : big_int -> 'a1 zipper -> 'a1 zipper c **)

let rec zip_rightn n z =
  (fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
    (fun _ -> z)
    (fun np -> zip_rightn np (zip_right z))
    n

(** val zip_leftn : big_int -> 'a1 zipper -> 'a1 zipper c **)

let rec zip_leftn n z =
  (fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))
    (fun _ ->
    z)
    (fun np ->
    zip_leftn np (zip_left z))
    n

(** val zip_minsert : 'a1 list -> 'a1 zipper -> 'a1 zipper c **)

let rec zip_minsert ma z =
  match ma with
  | Nil -> z
  | Cons (a, map) -> zip_minsert map (zip_insert z a)

(** val minsertz_at : 'a1 list -> big_int -> 'a1 list -> 'a1 list c **)

let rec minsertz_at ma n l =
  from_zip (zip_leftn n (zip_minsert ma (zip_rightn n (to_zip l))))

type color =
| BLACK
| RED

type 'a cTree =
| CT_leaf
| CT_node of 'a cTree * color * 'a * 'a cTree

(** val bst_search :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 cTree -> bool
    c **)

let rec bst_search a_cmp_dec a_eq_dec x = function
| CT_leaf -> true
| CT_node (l, c0, v, r) ->
  let filtered_var = a_eq_dec x v in
  (match filtered_var with
   | false -> false
   | true ->
     let filtered_var0 = a_cmp_dec x v in
     (match filtered_var0 with
      | false -> bst_search a_cmp_dec a_eq_dec x l
      | true -> bst_search a_cmp_dec a_eq_dec x r))

(** val rbt_blacken : 'a1 cTree -> 'a1 cTree c **)

let rec rbt_blacken ct = match ct with
| CT_leaf -> ct
| CT_node (l, c0, v, r) -> CT_node (l, BLACK, v, r)

(** val rbt_balance :
    'a1 cTree -> color -> 'a1 -> 'a1 cTree -> 'a1 cTree c **)

let rec rbt_balance tl tc tv tr =
  match tc with
  | BLACK ->
    (match tl with
     | CT_leaf ->
       (match tr with
        | CT_leaf -> CT_node (tl, tc, tv, tr)
        | CT_node (trl, trc, trv, trr) ->
          (match trc with
           | BLACK -> CT_node (tl, tc, tv, tr)
           | RED ->
             (match trl with
              | CT_leaf ->
                (match trr with
                 | CT_leaf -> CT_node (tl, tc, tv, tr)
                 | CT_node (trrl, trrc, trrv, trrr) ->
                   (match trrc with
                    | BLACK -> CT_node (tl, tc, tv, tr)
                    | RED ->
                      CT_node ((CT_node (tl, BLACK, tv, trl)), RED, trv,
                        (CT_node (trrl, BLACK, trrv, trrr)))))
              | CT_node (trll, trlc, trlv, trlr) ->
                (match trlc with
                 | BLACK ->
                   (match trr with
                    | CT_leaf -> CT_node (tl, tc, tv, tr)
                    | CT_node (trrl, trrc, trrv, trrr) ->
                      (match trrc with
                       | BLACK -> CT_node (tl, tc, tv, tr)
                       | RED ->
                         CT_node ((CT_node (tl, BLACK, tv, trl)), RED, trv,
                           (CT_node (trrl, BLACK, trrv, trrr)))))
                 | RED ->
                   CT_node ((CT_node (tl, BLACK, tv, trll)), RED, trlv,
                     (CT_node (trlr, BLACK, trv, trr)))))))
     | CT_node (tll, tlc, tlv, tlr) ->
       (match tlc with
        | BLACK ->
          (match tr with
           | CT_leaf -> CT_node (tl, tc, tv, tr)
           | CT_node (trl, trc, trv, trr) ->
             (match trc with
              | BLACK -> CT_node (tl, tc, tv, tr)
              | RED ->
                (match trl with
                 | CT_leaf ->
                   (match trr with
                    | CT_leaf -> CT_node (tl, tc, tv, tr)
                    | CT_node (trrl, trrc, trrv, trrr) ->
                      (match trrc with
                       | BLACK -> CT_node (tl, tc, tv, tr)
                       | RED ->
                         CT_node ((CT_node (tl, BLACK, tv, trl)), RED, trv,
                           (CT_node (trrl, BLACK, trrv, trrr)))))
                 | CT_node (trll, trlc, trlv, trlr) ->
                   (match trlc with
                    | BLACK ->
                      (match trr with
                       | CT_leaf -> CT_node (tl, tc, tv, tr)
                       | CT_node (trrl, trrc, trrv, trrr) ->
                         (match trrc with
                          | BLACK -> CT_node (tl, tc, tv, tr)
                          | RED ->
                            CT_node ((CT_node (tl, BLACK, tv, trl)), RED,
                              trv, (CT_node (trrl, BLACK, trrv, trrr)))))
                    | RED ->
                      CT_node ((CT_node (tl, BLACK, tv, trll)), RED, trlv,
                        (CT_node (trlr, BLACK, trv, trr)))))))
        | RED ->
          (match tll with
           | CT_leaf ->
             (match tlr with
              | CT_leaf ->
                (match tr with
                 | CT_leaf -> CT_node (tl, tc, tv, tr)
                 | CT_node (trl, trc, trv, trr) ->
                   (match trc with
                    | BLACK -> CT_node (tl, tc, tv, tr)
                    | RED ->
                      (match trl with
                       | CT_leaf ->
                         (match trr with
                          | CT_leaf -> CT_node (tl, tc, tv, tr)
                          | CT_node (trrl, trrc, trrv, trrr) ->
                            (match trrc with
                             | BLACK -> CT_node (tl, tc, tv, tr)
                             | RED ->
                               CT_node ((CT_node (tl, BLACK, tv, trl)), RED,
                                 trv, (CT_node (trrl, BLACK, trrv, trrr)))))
                       | CT_node (trll, trlc, trlv, trlr) ->
                         (match trlc with
                          | BLACK ->
                            (match trr with
                             | CT_leaf -> CT_node (tl, tc, tv, tr)
                             | CT_node (trrl, trrc, trrv, trrr) ->
                               (match trrc with
                                | BLACK -> CT_node (tl, tc, tv, tr)
                                | RED ->
                                  CT_node ((CT_node (tl, BLACK, tv, trl)),
                                    RED, trv, (CT_node (trrl, BLACK, trrv,
                                    trrr)))))
                          | RED ->
                            CT_node ((CT_node (tl, BLACK, tv, trll)), RED,
                              trlv, (CT_node (trlr, BLACK, trv, trr)))))))
              | CT_node (tlrl, tlrc, tlrv, tlrr) ->
                (match tlrc with
                 | BLACK ->
                   (match tr with
                    | CT_leaf -> CT_node (tl, tc, tv, tr)
                    | CT_node (trl, trc, trv, trr) ->
                      (match trc with
                       | BLACK -> CT_node (tl, tc, tv, tr)
                       | RED ->
                         (match trl with
                          | CT_leaf ->
                            (match trr with
                             | CT_leaf -> CT_node (tl, tc, tv, tr)
                             | CT_node (trrl, trrc, trrv, trrr) ->
                               (match trrc with
                                | BLACK -> CT_node (tl, tc, tv, tr)
                                | RED ->
                                  CT_node ((CT_node (tl, BLACK, tv, trl)),
                                    RED, trv, (CT_node (trrl, BLACK, trrv,
                                    trrr)))))
                          | CT_node (trll, trlc, trlv, trlr) ->
                            (match trlc with
                             | BLACK ->
                               (match trr with
                                | CT_leaf -> CT_node (tl, tc, tv, tr)
                                | CT_node (trrl, trrc, trrv, trrr) ->
                                  (match trrc with
                                   | BLACK -> CT_node (tl, tc, tv, tr)
                                   | RED ->
                                     CT_node ((CT_node (tl, BLACK, tv, trl)),
                                       RED, trv, (CT_node (trrl, BLACK, trrv,
                                       trrr)))))
                             | RED ->
                               CT_node ((CT_node (tl, BLACK, tv, trll)), RED,
                                 trlv, (CT_node (trlr, BLACK, trv, trr)))))))
                 | RED ->
                   CT_node ((CT_node (tll, BLACK, tlv, tlrl)), RED, tlrv,
                     (CT_node (tlrr, BLACK, tv, tr)))))
           | CT_node (tlll, tllc, tllv, tllr) ->
             (match tllc with
              | BLACK ->
                (match tlr with
                 | CT_leaf ->
                   (match tr with
                    | CT_leaf -> CT_node (tl, tc, tv, tr)
                    | CT_node (trl, trc, trv, trr) ->
                      (match trc with
                       | BLACK -> CT_node (tl, tc, tv, tr)
                       | RED ->
                         (match trl with
                          | CT_leaf ->
                            (match trr with
                             | CT_leaf -> CT_node (tl, tc, tv, tr)
                             | CT_node (trrl, trrc, trrv, trrr) ->
                               (match trrc with
                                | BLACK -> CT_node (tl, tc, tv, tr)
                                | RED ->
                                  CT_node ((CT_node (tl, BLACK, tv, trl)),
                                    RED, trv, (CT_node (trrl, BLACK, trrv,
                                    trrr)))))
                          | CT_node (trll, trlc, trlv, trlr) ->
                            (match trlc with
                             | BLACK ->
                               (match trr with
                                | CT_leaf -> CT_node (tl, tc, tv, tr)
                                | CT_node (trrl, trrc, trrv, trrr) ->
                                  (match trrc with
                                   | BLACK -> CT_node (tl, tc, tv, tr)
                                   | RED ->
                                     CT_node ((CT_node (tl, BLACK, tv, trl)),
                                       RED, trv, (CT_node (trrl, BLACK, trrv,
                                       trrr)))))
                             | RED ->
                               CT_node ((CT_node (tl, BLACK, tv, trll)), RED,
                                 trlv, (CT_node (trlr, BLACK, trv, trr)))))))
                 | CT_node (tlrl, tlrc, tlrv, tlrr) ->
                   (match tlrc with
                    | BLACK ->
                      (match tr with
                       | CT_leaf -> CT_node (tl, tc, tv, tr)
                       | CT_node (trl, trc, trv, trr) ->
                         (match trc with
                          | BLACK -> CT_node (tl, tc, tv, tr)
                          | RED ->
                            (match trl with
                             | CT_leaf ->
                               (match trr with
                                | CT_leaf -> CT_node (tl, tc, tv, tr)
                                | CT_node (trrl, trrc, trrv, trrr) ->
                                  (match trrc with
                                   | BLACK -> CT_node (tl, tc, tv, tr)
                                   | RED ->
                                     CT_node ((CT_node (tl, BLACK, tv, trl)),
                                       RED, trv, (CT_node (trrl, BLACK, trrv,
                                       trrr)))))
                             | CT_node (trll, trlc, trlv, trlr) ->
                               (match trlc with
                                | BLACK ->
                                  (match trr with
                                   | CT_leaf -> CT_node (tl, tc, tv, tr)
                                   | CT_node (trrl, trrc, trrv, trrr) ->
                                     (match trrc with
                                      | BLACK -> CT_node (tl, tc, tv, tr)
                                      | RED ->
                                        CT_node ((CT_node (tl, BLACK, tv,
                                          trl)), RED, trv, (CT_node (trrl,
                                          BLACK, trrv, trrr)))))
                                | RED ->
                                  CT_node ((CT_node (tl, BLACK, tv, trll)),
                                    RED, trlv, (CT_node (trlr, BLACK, trv,
                                    trr)))))))
                    | RED ->
                      CT_node ((CT_node (tll, BLACK, tlv, tlrl)), RED, tlrv,
                        (CT_node (tlrr, BLACK, tv, tr)))))
              | RED ->
                CT_node ((CT_node (tlll, BLACK, tllv, tllr)), RED, tlv,
                  (CT_node (tlr, BLACK, tv, tr)))))))
  | RED -> CT_node (tl, tc, tv, tr)

(** val rbt_insert_inner :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 cTree -> 'a1 -> 'a1
    cTree c **)

let rec rbt_insert_inner a_cmp_dec a_eq_dec ct x =
  match ct with
  | CT_leaf -> CT_node (ct, RED, x, ct)
  | CT_node (l, c0, v, r) ->
    let filtered_var = a_eq_dec x v in
    (match filtered_var with
     | false -> ct
     | true ->
       let filtered_var0 = a_cmp_dec x v in
       (match filtered_var0 with
        | false ->
          rbt_balance (rbt_insert_inner a_cmp_dec a_eq_dec l x) c0 v r
        | true ->
          rbt_balance l c0 v (rbt_insert_inner a_cmp_dec a_eq_dec r x)))

(** val rbt_insert :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 cTree -> 'a1 -> 'a1
    cTree c **)

let rec rbt_insert a_cmp_dec a_eq_dec ct x =
  rbt_blacken (rbt_insert_inner a_cmp_dec a_eq_dec ct x)

