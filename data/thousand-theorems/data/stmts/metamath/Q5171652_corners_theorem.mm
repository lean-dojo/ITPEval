$(
  Statement-only formalization of Thousand Theorems corpus artifact Q5171652
  (thousand-theorems__metamath__Q5171652), "Corners theorem": every
  sufficiently dense finite subset of an initial square of natural-number
  pairs contains a nontrivial corner once the side length meets the explicit
  bound. This file contains no proof.
$)

$[ lib/set.mm $]

$c Q5171652NatFloor Q5171652NatCeil Q5171652Inv Q5171652Max
   Q5171652Min Q5171652Step Q5171652Initial Q5171652Regularity
   Q5171652Triangle Q5171652Bound $.

q5171652-nat-floor-syntax $a class ( Q5171652NatFloor x ) $.
q5171652-nat-ceil-syntax $a class ( Q5171652NatCeil x ) $.
q5171652-inv-syntax $a class ( Q5171652Inv x ) $.
q5171652-max-syntax $a class ( Q5171652Max A B ) $.
q5171652-min-syntax $a class ( Q5171652Min A B ) $.
q5171652-step-syntax $a class Q5171652Step $.
q5171652-initial-syntax $a class ( Q5171652Initial x A ) $.
q5171652-regularity-syntax $a class ( Q5171652Regularity x A ) $.
q5171652-triangle-syntax $a class ( Q5171652Triangle x ) $.
q5171652-bound-syntax $a class ( Q5171652Bound x ) $.

$(
  Natural floor and ceiling are totalized as in Lean's Nat.floor and
  Nat.ceil.  Q5171652Inv records Lean's total inverse convention.
$)
q5171652-nat-floor-definition $a
  |- ( Q5171652NatFloor x ) = if ( x < 0 , 0 , ( |_ ` x ) ) $.

q5171652-nat-ceil-definition $a
  |- ( Q5171652NatCeil x ) =
      if ( x <_ 0 , 0 ,
        if ( x = ( |_ ` x ) , ( |_ ` x ) , ( ( |_ ` x ) + 1 ) ) ) $.

q5171652-inv-definition $a
  |- ( Q5171652Inv x ) = if ( x = 0 , 0 , ( 1 / x ) ) $.

q5171652-max-definition $a
  |- ( Q5171652Max A B ) = if ( A <_ B , B , A ) $.

q5171652-min-definition $a
  |- ( Q5171652Min A B ) = if ( A <_ B , A , B ) $.

q5171652-step-definition $a
  |- Q5171652Step = ( k e. NN0 |-> ( k x. ( 4 ^ k ) ) ) $.

q5171652-initial-definition $a
  |- ( Q5171652Initial x A ) =
      ( Q5171652Max 7
        ( Q5171652Max A
          ( ( Q5171652NatFloor
              ( ( log ` ( ( ( 2 x. 5 ) ^ 2 ) / ( x ^ 5 ) ) )
                / ( log ` 4 ) ) ) + 1 ) ) ) $.

q5171652-regularity-definition $a
  |- ( Q5171652Regularity x A ) =
      ( ( ( ( IterComp ` Q5171652Step )
              ` ( Q5171652NatFloor ( 4 / ( x ^ 5 ) ) ) )
            ` ( Q5171652Initial x A ) )
        x.
        ( ( 4 ^ 2 ) ^
          ( ( ( IterComp ` Q5171652Step )
                ` ( Q5171652NatFloor ( 4 / ( x ^ 5 ) ) ) )
              ` ( Q5171652Initial x A ) ) ) ) $.

q5171652-triangle-definition $a
  |- ( Q5171652Triangle x ) =
      ( Q5171652Min
        ( Q5171652Inv
          ( 2 x. ( ( Q5171652NatCeil ( 4 / x ) ) ^ 3 ) ) )
        ( ( 1 - ( ( Q5171652Min 1 x ) / 4 ) )
          x.
          ( ( x /
              ( ( 4 ^ 2 ) x.
                ( Q5171652Regularity
                  ( x / 8 ) ( Q5171652NatCeil ( 4 / x ) ) ) ) ) ^ 3 ) ) ) $.

q5171652-bound-definition $a
  |- ( Q5171652Bound x ) =
      ( ( Q5171652NatFloor
          ( Q5171652Inv
            ( ( Q5171652Triangle ( x / 9 ) ) x. ( 3 ^ 3 ) ) ) ) + 1 ) $.

$(
  This is corners_theorem_nat.  The source conclusion that the set is not
  corner-free is written in its definitionally equivalent witness form:
  three points of A form a corner and its two horizontal coordinates differ.
  The theorem applies Q5171652Bound to e / 9, while that definition applies
  Q5171652Triangle to its own argument divided by 9, preserving the source's
  two nested divisions by 9.  The final declaration is an unproved $a
  statement; this database contains no $p proof statement.
$)
${
  $d A e n w x y z $.
  q5171652-corners-theorem $a
    |- A. e e. RR A. n e. NN0 A. A e. Fin
       ( ( ( 0 < e /\ ( Q5171652Bound ( e / 9 ) ) <_ n )
           /\
           ( A C_ ( ( 0 ..^ n ) X. ( 0 ..^ n ) )
             /\ ( e x. ( n ^ 2 ) ) <_ ( # ` A ) ) )
         ->
         E. x e. NN0 E. y e. NN0 E. z e. NN0 E. w e. NN0
           ( ( ( <. x , y >. e. A /\ <. x , w >. e. A )
               /\ <. z , y >. e. A )
             /\ ( ( x + w ) = ( z + y ) /\ x =/= z ) ) ) $.
$}
