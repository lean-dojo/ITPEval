(*
  Statement-only formalization of "The Four Color Problem" from Hundred
  Theorems item 032. It states the finite and general four-color claims for
  simple topological maps over every complete ordered-field real model.
  This file contains no proof.
*)

let FOUR_COLOR_PROBLEM =
 `!rle:A->A->bool
    rsup:(A->bool)->A
    radd:A->A->A
    rzero:A
    ropp:A->A
    rmul:A->A->A
    rone:A
    rinv:A->A.
  let real_eq = \x y:A. rle x y /\ rle y x in
  let rhas_sup =
    \e:A->bool.
      (?x. e x) /\ (?z. !y. e y ==> rle y z) in
  let real_model_axioms =
   ((!x. rle x x) /\
    (!x y z. rle x y /\ rle y z ==> rle x z) /\
    (!e:A->bool.
       rhas_sup e ==> !y. e y ==> rle y (rsup e)) /\
    (!e:A->bool x.
       rhas_sup e
       ==> ((?y. e y /\ rle x y) \/ rle (rsup e) x)) /\
    (!x y z. rle y z ==> rle (radd x y) (radd x z)) /\
    (!x y. real_eq (radd x y) (radd y x)) /\
    (!x y z.
       real_eq (radd x (radd y z)) (radd (radd x y) z)) /\
    (!x. real_eq (radd rzero x) x) /\
    (!x. real_eq (radd x (ropp x)) rzero) /\
    (!x y z.
       rle rzero x /\ rle y z ==> rle (rmul x y) (rmul x z)) /\
    (!x y. real_eq (rmul x y) (rmul y x)) /\
    (!x y z.
       real_eq (rmul x (rmul y z)) (rmul (rmul x y) z)) /\
    (!x y z.
       real_eq (rmul x (radd y z))
               (radd (rmul x y) (rmul x z))) /\
    (!x. real_eq (rmul rone x) x) /\
    (!x. ~(real_eq x rzero)
         ==> real_eq (rmul x (rinv x)) rone) /\
    ~(real_eq rone rzero)) in
  let strict = \x y:A. ~(rle y x) in
  let open_region =
    \s:(A#A)->bool.
      !p. s p
          ==> ?xl xu yl yu:A.
                strict xl (FST p) /\ strict (FST p) xu /\
                strict yl (SND p) /\ strict (SND p) yu /\
                (!q. strict xl (FST q) /\ strict (FST q) xu /\
                     strict yl (SND q) /\ strict (SND q) yu
                     ==> s q) in
  let closure_region =
    \s:(A#A)->bool. \p:A#A.
      !u:(A#A)->bool.
        open_region u /\ u p ==> ?q. s q /\ u q in
  let connected_region =
    \s:(A#A)->bool.
      !u v:(A#A)->bool.
        open_region u /\
        open_region v /\
        (!x. s x ==> u x \/ v x) /\
        (?x. u x /\ s x) /\
        (?x. v x /\ s x)
        ==> ?x. u x /\ v x in
  let plain_map =
    \m:(A#A)->(A#A)->bool.
      (!p q. m p q ==> m q p) /\
      (!p q r. m p q /\ m q r ==> m p r) in
  let at_most_regions =
    \n:num. \m:(A#A)->(A#A)->bool.
      ?representative:num->(A#A).
        !p. m p p ==> ?i. i < n /\ m (representative i) p in
  let simple_map =
    \m:(A#A)->(A#A)->bool.
      plain_map m /\
      (!p. open_region (m p)) /\
      (!p. connected_region (m p)) in
  let finite_simple_map =
    \m:(A#A)->(A#A)->bool.
      simple_map m /\ ?n. at_most_regions n m in
  let border =
    \m:(A#A)->(A#A)->bool.
    \p q:A#A. \x:A#A.
      closure_region (m p) x /\ closure_region (m q) x in
  let corner_map =
    \m:(A#A)->(A#A)->bool.
    \p:A#A. \q r:A#A.
      m q r /\ closure_region (m q) p in
  let not_corner =
    \m:(A#A)->(A#A)->bool. \p:A#A.
      at_most_regions 2 (corner_map m p) in
  let adjacent =
    \m:(A#A)->(A#A)->bool. \p q:A#A.
      ~(m p q) /\ ?x. not_corner m x /\ border m p q x in
  let coloring =
    \m:(A#A)->(A#A)->bool.
    \k:(A#A)->(A#A)->bool.
      plain_map k /\
      (!p. k p p ==> m p p) /\
      (!p q. m p q ==> k p q) /\
      (!p q. adjacent m p q ==> ~(k p q)) in
  let colorable_with =
    \n:num. \m:(A#A)->(A#A)->bool.
      ?k:(A#A)->(A#A)->bool.
        coloring m k /\ at_most_regions n k in
  real_model_axioms
  ==>
  ((!m:(A#A)->(A#A)->bool.
       finite_simple_map m ==> colorable_with 4 m) /\
   (!m:(A#A)->(A#A)->bool.
       simple_map m ==> colorable_with 4 m))`;;
