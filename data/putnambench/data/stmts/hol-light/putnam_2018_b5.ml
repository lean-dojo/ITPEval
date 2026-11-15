(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_b5
  (putnambench__hol-light__putnam_2018_b5): a continuously differentiable
  map from the real plane to itself is injective under positivity of all first
  partial derivatives and the stated pointwise quadratic inequality. This
  file contains no proof.
*)

let statement =
  `let coordinate =
     \(i:num) (p:real#real).
       if i = 1 then FST p else SND p in
   let replace_coordinate =
     \(p:real#real) (i:num) (t:real).
       if i = 1 then (t,SND p) else (FST p,t) in
   let has_derivative_at =
     \(g:real->real) (d:real) (x:real).
       !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 &0 < abs (y - x) /\ abs (y - x) < delta
                 ==> abs ((g y - g x) / (y - x) - d) < e in
   let continuous_on_plane =
     \(g:(real#real)->real).
       !p:real#real. !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !q:real#real.
                 abs (FST q - FST p) < delta /\
                 abs (SND q - SND p) < delta
                 ==> abs (g q - g p) < e in
   let partial =
     \(f:(real#real)->(real#real)) (i:num) (j:num) (p:real#real).
       @d:real.
         has_derivative_at
           (\t:real.
              coordinate i (f (replace_coordinate p j t)))
           d (coordinate j p) in
   let continuously_differentiable =
     \(f:(real#real)->(real#real)).
       !i j:num.
         1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
         ==>
         (!p:real#real.
            has_derivative_at
              (\t:real.
                 coordinate i (f (replace_coordinate p j t)))
              (partial f i j p) (coordinate j p)) /\
         continuous_on_plane (partial f i j) in
   !f:(real#real)->(real#real).
     continuously_differentiable f /\
     (!p:real#real. !i j:num.
        1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
        ==> &0 < partial f i j p) /\
     (!p:real#real.
        &0 <
        partial f 1 1 p * partial f 2 2 p -
        (&1 / &4) *
        (partial f 1 2 p + partial f 2 1 p) pow 2)
     ==>
     !p q:real#real. f p = f q ==> p = q`;;
