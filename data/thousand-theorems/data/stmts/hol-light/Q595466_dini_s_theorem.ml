(*
  Statement-only formalization of Thousand Theorems corpus artifact Q595466,
  "Dini's theorem": a monotone family of continuous functions into a
  solid-normed lattice ordered additive commutative group that converges
  pointwise along an arbitrary preorder converges locally uniformly. This file
  contains no proof.
*)

let Q595466_DINI_S_THEOREM =
 `let preorder_on =
      \(carrier:'i->bool) (le:'i->'i->bool).
        (!i:'i. carrier i ==> le i i) /\
        (!i j k:'i.
           carrier i /\ carrier j /\ carrier k /\
           le i j /\ le j k
           ==> le i k) in
   let topology_on =
      \(carrier:'a->bool) (opens:('a->bool)->bool).
        opens (\x:'a. F) /\
        opens carrier /\
        (!s:'a->bool.
           opens s ==> !x:'a. s x ==> carrier x) /\
        (!s t:'a->bool.
           opens s /\ opens t
           ==> opens (\x:'a. s x /\ t x)) /\
        (!family:('a->bool)->bool.
           (!s:'a->bool. family s ==> opens s)
           ==> opens
                 (\x:'a. ?s:'a->bool. family s /\ s x)) in
   let filter_on =
      \(carrier:'i->bool) (eventually:('i->bool)->bool).
        eventually carrier /\
        (!s t:'i->bool.
           eventually s /\
           (!i:'i. carrier i /\ s i ==> t i)
           ==> eventually t) /\
        (!s t:'i->bool.
           eventually s /\ eventually t
           ==> eventually (\i:'i. s i /\ t i)) in
   let at_top =
      \(carrier:'i->bool) (le:'i->'i->bool)
       (eventually:('i->bool)->bool).
        filter_on carrier eventually /\
        (!i:'i.
           carrier i
           ==> eventually
                 (\j:'i. carrier j /\ le i j)) /\
        (!other:('i->bool)->bool.
           filter_on carrier other /\
           (!i:'i.
              carrier i
              ==> other
                    (\j:'i. carrier j /\ le i j))
           ==> !s:'i->bool.
                 eventually s ==> other s) in
   let normed_add_comm_group_on =
      \(carrier:'g->bool) (zero:'g) (add:'g->'g->'g)
       (neg:'g->'g) (norm:'g->real).
        carrier zero /\
        (!x:'g. carrier x ==> carrier (neg x)) /\
        (!x y:'g.
           carrier x /\ carrier y
           ==> carrier (add x y)) /\
        (!x y:'g.
           carrier x /\ carrier y
           ==> add x y = add y x) /\
        (!x y z:'g.
           carrier x /\ carrier y /\ carrier z
           ==> add (add x y) z = add x (add y z)) /\
        (!x:'g.
           carrier x ==> add x zero = x) /\
        (!x:'g.
           carrier x ==> add x (neg x) = zero) /\
        (!x:'g.
           carrier x ==> &0 <= norm x) /\
        (!x:'g.
           carrier x ==> (norm x = &0 <=> x = zero)) /\
        (!x:'g.
           carrier x ==> norm (neg x) = norm x) /\
        (!x y:'g.
           carrier x /\ carrier y
           ==> norm (add x y) <= norm x + norm y) in
   let lattice_on =
      \(carrier:'g->bool) (le:'g->'g->bool)
       (join:'g->'g->'g) (meet:'g->'g->'g).
        (!x:'g. carrier x ==> le x x) /\
        (!x y z:'g.
           carrier x /\ carrier y /\ carrier z /\
           le x y /\ le y z
           ==> le x z) /\
        (!x y:'g.
           carrier x /\ carrier y /\ le x y /\ le y x
           ==> x = y) /\
        (!x y:'g.
           carrier x /\ carrier y
           ==> carrier (join x y) /\
               le x (join x y) /\
               le y (join x y) /\
               (!z:'g.
                  carrier z /\ le x z /\ le y z
                  ==> le (join x y) z)) /\
        (!x y:'g.
           carrier x /\ carrier y
           ==> carrier (meet x y) /\
               le (meet x y) x /\
               le (meet x y) y /\
               (!z:'g.
                  carrier z /\ le z x /\ le z y
                  ==> le z (meet x y))) in
   let ordered_add_monoid_on =
      \(carrier:'g->bool) (le:'g->'g->bool)
       (add:'g->'g->'g).
        !x y z:'g.
          carrier x /\ carrier y /\ carrier z /\ le x y
          ==> le (add x z) (add y z) in
   let solid_norm_on =
      \(carrier:'g->bool) (le:'g->'g->bool)
       (join:'g->'g->'g) (neg:'g->'g) (norm:'g->real).
        !x y:'g.
          carrier x /\ carrier y /\
          le (join x (neg x)) (join y (neg y))
          ==> norm x <= norm y in
   let continuous =
      \(acarrier:'a->bool) (gcarrier:'g->bool)
       (opens:('a->bool)->bool) (add:'g->'g->'g)
       (neg:'g->'g) (norm:'g->real) (h:'a->'g).
        (!x:'a. acarrier x ==> gcarrier (h x)) /\
        (!x:'a.
           acarrier x
           ==> !epsilon:real.
                 &0 < epsilon
                 ==> ?u:'a->bool.
                       opens u /\ u x /\
                       (!y:'a.
                          u y
                          ==> norm
                                (add (h y) (neg (h x))) <
                              epsilon)) in
   let pointwise_tends =
      \(acarrier:'a->bool)
       (eventually:('i->bool)->bool)
       (add:'g->'g->'g) (neg:'g->'g) (norm:'g->real)
       (funcs:'i->'a->'g) (f:'a->'g).
        !x:'a.
          acarrier x
          ==> !epsilon:real.
                &0 < epsilon
                ==> eventually
                      (\i:'i.
                         norm
                           (add (funcs i x) (neg (f x))) <
                         epsilon) in
   let locally_uniformly_tends =
      \(acarrier:'a->bool) (opens:('a->bool)->bool)
       (eventually:('i->bool)->bool)
       (add:'g->'g->'g) (neg:'g->'g) (norm:'g->real)
       (funcs:'i->'a->'g) (f:'a->'g).
        !epsilon:real.
          &0 < epsilon
          ==> !x:'a.
                acarrier x
                ==> ?u:'a->bool.
                      opens u /\ u x /\
                      eventually
                        (\i:'i.
                           !y:'a.
                             u y
                             ==> norm
                                   (add (funcs i y)
                                     (neg (f y))) <
                                 epsilon) in
   !icarrier:'i->bool
    acarrier:'a->bool
    gcarrier:'g->bool
    ile:'i->'i->bool
    opens:('a->bool)->bool
    eventually:('i->bool)->bool
    zero:'g
    add:'g->'g->'g
    neg:'g->'g
    norm:'g->real
    gle:'g->'g->bool
    join:'g->'g->'g
    meet:'g->'g->'g
    funcs:'i->'a->'g
    f:'a->'g.
      preorder_on icarrier ile /\
      topology_on acarrier opens /\
      at_top icarrier ile eventually /\
      normed_add_comm_group_on
        gcarrier zero add neg norm /\
      lattice_on gcarrier gle join meet /\
      ordered_add_monoid_on gcarrier gle add /\
      solid_norm_on gcarrier gle join neg norm /\
      (!i:'i.
         icarrier i
         ==> continuous
               acarrier gcarrier opens add neg norm
               (funcs i)) /\
      (!i j:'i.
         icarrier i /\ icarrier j /\ ile i j
         ==> !x:'a.
               acarrier x
               ==> gle (funcs i x) (funcs j x)) /\
      continuous acarrier gcarrier opens add neg norm f /\
      pointwise_tends
        acarrier eventually add neg norm funcs f
      ==> locally_uniformly_tends
            acarrier opens eventually add neg norm funcs f`;;
