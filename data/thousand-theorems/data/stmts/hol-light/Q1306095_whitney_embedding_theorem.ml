(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1306095,
  "Whitney embedding theorem": every compact Hausdorff smooth
  finite-dimensional real manifold, including a manifold with corners, has a
  smooth closed embedding into some finite-dimensional Euclidean space whose
  intrinsic manifold differential is injective at every point. This file
  contains no proof.
*)

let Q1306095_WHITNEY_EMBEDDING_THEOREM =
 `let supported =
    \(d:num) (x:num->real).
      !i:num. d <= i ==> x i = &0 in
  let vzero =
    \i:num. &0 in
  let vadd =
    \(x:num->real) (y:num->real) i. x i + y i in
  let vsub =
    \(x:num->real) (y:num->real) i. x i - y i in
  let vsmul =
    \(a:real) (x:num->real) i. a * x i in
  let dot =
    \(d:num) (x:num->real) (y:num->real).
      sum {i:num | i < d} (\i. x i * y i) in
  let sqdist =
    \(d:num) (x:num->real) (y:num->real).
      sum {i:num | i < d} (\i. (x i - y i) pow 2) in
  let euclidean_open =
    \(d:num) (s:(num->real)->bool).
      (!x:num->real. x IN s ==> supported d x) /\
      (!x:num->real.
         x IN s
         ==> ?epsilon:real.
               &0 < epsilon /\
               !y:num->real.
                 supported d y /\
                 sqdist d x y < epsilon pow 2
                 ==> y IN s) in
  let relative_open =
    \(d:num) (model:(num->real)->bool)
     (s:(num->real)->bool).
      s SUBSET model /\
      (!x:num->real.
         x IN s
         ==> ?epsilon:real.
               &0 < epsilon /\
               !y:num->real.
                 y IN model /\
                 sqdist d x y < epsilon pow 2
                 ==> y IN s) in
  let linear_map =
    \(d:num) (m:num) (l:(num->real)->num->real).
      (!x:num->real. supported d x ==> supported m (l x)) /\
      (!x y:num->real.
         supported d x /\ supported d y
         ==> l (vadd x y) = vadd (l x) (l y)) /\
      (!a:real. !x:num->real.
         supported d x
         ==> l (vsmul a x) = vsmul a (l x)) in
  let has_scalar_derivative =
    \(d:num) (f:(num->real)->real)
     (domain:(num->real)->bool) (x:num->real)
     (gradient:num->real).
      supported d gradient /\
      (!epsilon:real.
         &0 < epsilon
         ==> ?delta:real.
               &0 < delta /\
               !y:num->real.
                 y IN domain /\
                 &0 < sqdist d x y /\
                 sqdist d x y < delta pow 2
                 ==> (f y - f x -
                      dot d gradient (vsub y x)) pow 2
                     < epsilon pow 2 * sqdist d x y) in
  let has_vector_derivative =
    \(d:num) (m:num) (f:(num->real)->num->real)
     (domain:(num->real)->bool) (x:num->real)
     (l:(num->real)->num->real).
      linear_map d m l /\
      (!epsilon:real.
         &0 < epsilon
         ==> ?delta:real.
               &0 < delta /\
               !y:num->real.
                 y IN domain /\
                 &0 < sqdist d x y /\
                 sqdist d x y < delta pow 2
                 ==> sqdist m
                       (vsub (vsub (f y) (f x))
                             (l (vsub y x)))
                       vzero
                     < epsilon pow 2 * sqdist d x y) in
	  let intrinsic_vector_derivative =
	    \(d:num) (m:num) (f:(num->real)->num->real)
	     (domain:(num->real)->bool) (x:num->real)
	     (l:(num->real)->num->real).
      has_vector_derivative d m f domain x l /\
      (!l':(num->real)->num->real.
         has_vector_derivative d m f domain x l'
	         ==> !v:num->real.
	               supported d v ==> l' v = l v) in
	  let scalar_continuous_within =
	    \(d:num) (f:(num->real)->real)
	     (domain:(num->real)->bool) (x:num->real).
	      !epsilon:real.
	        &0 < epsilon
	        ==> ?delta:real.
	              &0 < delta /\
	              !y:num->real.
	                y IN domain /\
	                sqdist d x y < delta pow 2
	                ==> (f y - f x) pow 2 < epsilon pow 2 in
	  let jet_index =
	    \(d:num) (m:num) (k:num) (alpha:num list).
	      LENGTH alpha = SUC k /\
	      HD alpha < m /\
	      (!r:num. r < k ==> EL (SUC r) alpha < d) in
	  let finite_order_jet =
	    \(d:num) (m:num) (order:num)
	     (domain:(num->real)->bool)
	     (f:(num->real)->num->real).
	      (!x:num->real. x IN domain ==> supported m (f x)) /\
	      ?jet:num->(num->real)->num list->real.
	        (!x:num->real. !j:num.
	           x IN domain /\ j < m ==> jet 0 x [j] = f x j) /\
	        (!k:num. !alpha:num list.
	           k <= order /\ jet_index d m k alpha
	           ==> !x:num->real.
	                 x IN domain
	                 ==> scalar_continuous_within d
	                       (\y:num->real. jet k y alpha)
	                       domain x) /\
	        (!k:num. !alpha:num list.
	           k < order /\ jet_index d m k alpha
	           ==> !x:num->real.
	                 x IN domain
	                 ==> has_scalar_derivative d
	                       (\y:num->real. jet k y alpha)
	                       domain x
	                       (\i:num. jet (SUC k) x (APPEND alpha [i]))) in
	  let relative_neighborhood =
	    \(d:num) (s:(num->real)->bool) (x:num->real)
	     (u:(num->real)->bool).
	      u SUBSET s /\
	      x IN u /\
	      ?epsilon:real.
	        &0 < epsilon /\
	        !y:num->real.
	          y IN s /\ sqdist d x y < epsilon pow 2
	          ==> y IN u in
	  let cont_diff_infinity_within_at =
	    \(d:num) (m:num) (f:(num->real)->num->real)
	     (s:(num->real)->bool) (x:num->real).
	      x IN s /\
	      !order:num.
	        ?u:(num->real)->bool.
	          relative_neighborhood d s x u /\
	          finite_order_jet d m order u f in
  let model_with_corners_range =
    \(d:num) (model:(num->real)->bool).
      (!x:num->real. x IN model ==> supported d x) /\
      (!x y:num->real.
         x IN model /\ y IN model
         ==> !a b:real.
               &0 <= a /\ &0 <= b /\ a + b = &1
               ==> vadd (vsmul a x) (vsmul b y) IN model) /\
      (?x:num->real.
         x IN model /\
         ?epsilon:real.
           &0 < epsilon /\
           !y:num->real.
             supported d y /\
             sqdist d x y < epsilon pow 2
             ==> y IN model) in
  let is_topology =
    \(carrier:A->bool) (open_sets:(A->bool)->bool).
      open_sets {} /\
      open_sets carrier /\
      (!u:A->bool. open_sets u ==> u SUBSET carrier) /\
      (!c:(A->bool)->bool.
         (!u:A->bool. u IN c ==> open_sets u)
         ==> open_sets (UNIONS c)) /\
      (!u v:A->bool.
         open_sets u /\ open_sets v
         ==> open_sets (u INTER v)) in
  let open_in_space =
    \(carrier:A->bool) (open_sets:(A->bool)->bool)
     (s:A->bool) (u:A->bool).
      u SUBSET s /\
      ?v:A->bool. open_sets v /\ u = s INTER v in
  let compact_space =
    \(carrier:A->bool) (open_sets:(A->bool)->bool).
      !cover:(A->bool)->bool.
        (!u:A->bool. u IN cover ==> open_sets u) /\
        carrier SUBSET UNIONS cover
        ==> ?finite_cover:(A->bool)->bool.
              FINITE finite_cover /\
              finite_cover SUBSET cover /\
              carrier SUBSET UNIONS finite_cover in
  let hausdorff_space =
    \(carrier:A->bool) (open_sets:(A->bool)->bool).
      !x y:A.
        x IN carrier /\ y IN carrier /\ ~(x = y)
        ==> ?u v:A->bool.
              open_sets u /\ open_sets v /\
              x IN u /\ y IN v /\ u INTER v = {} in
  let chart_atlas =
    \(d:num) (model:(num->real)->bool)
     (carrier:A->bool) (open_sets:(A->bool)->bool)
     (source:K->A->bool)
     (target:K->(num->real)->bool)
     (chart:K->A->num->real)
     (chart_inv:K->(num->real)->A).
      (!x:A. x IN carrier ==> ?p:K. x IN source p) /\
      (!p:K.
         open_sets (source p) /\
         source p SUBSET carrier /\
         relative_open d model (target p) /\
         (!x:A.
            x IN source p
            ==> chart p x IN target p /\
                chart_inv p (chart p x) = x) /\
         (!y:num->real.
            y IN target p
            ==> chart_inv p y IN source p /\
                chart p (chart_inv p y) = y) /\
         (!v:(num->real)->bool.
            relative_open d (target p) v
            ==> open_in_space carrier open_sets (source p)
                  {x:A | x IN source p /\ chart p x IN v}) /\
         (!u:A->bool.
            open_in_space carrier open_sets (source p) u
            ==> relative_open d (target p)
                  {y:num->real |
                     y IN target p /\ chart_inv p y IN u})) in
	  let smooth_atlas =
	    \(d:num) (source:K->A->bool)
	     (target:K->(num->real)->bool)
	     (chart:K->A->num->real)
	     (chart_inv:K->(num->real)->A).
	      !p q:K. !x:A.
	        x IN source p /\ x IN source q
	        ==> cont_diff_infinity_within_at d d
	              (\y:num->real. chart q (chart_inv p y))
	              {y:num->real |
	                 y IN target p /\ chart_inv p y IN source q}
	              (chart p x) in
  let is_smooth_manifold =
    \(d:num) (model:(num->real)->bool)
     (carrier:A->bool) (open_sets:(A->bool)->bool)
     (source:K->A->bool)
     (target:K->(num->real)->bool)
     (chart:K->A->num->real)
     (chart_inv:K->(num->real)->A).
      is_topology carrier open_sets /\
      model_with_corners_range d model /\
      chart_atlas d model carrier open_sets
        source target chart chart_inv /\
      smooth_atlas d source target chart chart_inv in
  let closed_embedding =
    \(n:num) (carrier:A->bool) (open_sets:(A->bool)->bool)
     (e:A->num->real).
      (!x:A. x IN carrier ==> supported n (e x)) /\
      (!x y:A.
         x IN carrier /\ y IN carrier /\ e x = e y ==> x = y) /\
      (!u:A->bool.
         open_sets u <=>
         ?v:(num->real)->bool.
           euclidean_open n v /\
           u = {x:A | x IN carrier /\ e x IN v}) /\
      relative_open n
        {z:num->real | supported n z}
        ({z:num->real | supported n z} DIFF
         {z:num->real | ?x:A. x IN carrier /\ z = e x}) in
  let smooth_immersion =
    \(d:num) (n:num) (carrier:A->bool)
     (source:K->A->bool)
     (target:K->(num->real)->bool)
     (chart:K->A->num->real)
     (chart_inv:K->(num->real)->A)
	     (e:A->num->real).
	      !x:A.
	        x IN carrier
	        ==> ?p:K.
	            ?derivative:(num->real)->num->real.
	              x IN source p /\
	              cont_diff_infinity_within_at d n
	                (\y:num->real. e (chart_inv p y))
	                (target p) (chart p x) /\
	              intrinsic_vector_derivative d n
	                (\y:num->real. e (chart_inv p y))
                (target p) (chart p x) derivative /\
              (!v:num->real.
                 supported d v /\ derivative v = vzero
                 ==> v = vzero) in
  !d:num.
  !model:(num->real)->bool.
  !carrier:A->bool.
  !open_sets:(A->bool)->bool.
  !source:K->A->bool.
  !target:K->(num->real)->bool.
  !chart:K->A->num->real.
  !chart_inv:K->(num->real)->A.
    is_smooth_manifold d model carrier open_sets
      source target chart chart_inv /\
    hausdorff_space carrier open_sets /\
    compact_space carrier open_sets
    ==> ?n:num. ?e:A->num->real.
          closed_embedding n carrier open_sets e /\
          smooth_immersion d n carrier source target
            chart chart_inv e`;;
