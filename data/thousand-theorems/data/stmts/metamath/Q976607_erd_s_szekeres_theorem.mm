$(
  Statement-only formalization of Thousand Theorems corpus artifact Q976607
  (thousand-theorems__metamath__Q976607),
  "Erd&odblac;s&ndash;Szekeres theorem": an
  injective sequence indexed by a finite linear order with more than r * s
  entries has an increasing subsequence longer than r or a decreasing
  subsequence longer than s. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary Lean types are represented by set carriers I and A. Their
  linear orders are represented by relations Q and R with reflexivity,
  antisymmetry, transitivity, and totality stated explicitly. Strict order is
  the corresponding non-strict relation together with inequality.

  A subset of the finite carrier I is finite, so the two existential subsets
  are exactly Lean Finsets. Their all-pairs conditions are StrictMonoOn and
  StrictAntiOn for f. The following declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

${
  $d A I Q R S T f i j k r s x y z $.

  thousand-theorems-q976607-erdos-szekeres $a
  |- A. I A. Q A. A A. R
       A. r e. NN0
         A. s e. NN0
           A. f
             (
               (
                 (
                   I e. Fin
                   /\
                   (
                     Q C_ ( I X. I )
                     /\
                     (
                       A. i e. I <. i , i >. e. Q
                       /\
                       (
                         A. i e. I A. j e. I
                           (
                             ( <. i , j >. e. Q /\ <. j , i >. e. Q )
                             ->
                             i = j
                           )
                         /\
                         (
                           A. i e. I A. j e. I A. k e. I
                             (
                               ( <. i , j >. e. Q /\ <. j , k >. e. Q )
                               ->
                               <. i , k >. e. Q
                             )
                           /\
                           A. i e. I A. j e. I
                             ( <. i , j >. e. Q \/ <. j , i >. e. Q )
                         )
                       )
                     )
                   )
                 )
                 /\
                 (
                   (
                     R C_ ( A X. A )
                     /\
                     (
                       A. x e. A <. x , x >. e. R
                       /\
                       (
                         A. x e. A A. y e. A
                           (
                             ( <. x , y >. e. R /\ <. y , x >. e. R )
                             ->
                             x = y
                           )
                         /\
                         (
                           A. x e. A A. y e. A A. z e. A
                             (
                               ( <. x , y >. e. R /\ <. y , z >. e. R )
                               ->
                               <. x , z >. e. R
                             )
                           /\
                           A. x e. A A. y e. A
                             ( <. x , y >. e. R \/ <. y , x >. e. R )
                         )
                       )
                     )
                   )
                   /\
                   (
                     f : I --> A
                     /\
                     (
                       A. i e. I A. j e. I
                         ( ( f ` i ) = ( f ` j ) -> i = j )
                       /\
                       ( r x. s ) < ( # ` I )
                     )
                   )
                 )
               )
               ->
               (
                 E. S
                   (
                     S C_ I
                     /\
                     (
                       r < ( # ` S )
                       /\
                       A. i e. S A. j e. S
                         (
                           (
                             <. i , j >. e. Q
                             /\
                             i =/= j
                           )
                           ->
                           (
                             <. ( f ` i ) , ( f ` j ) >. e. R
                             /\
                             ( f ` i ) =/= ( f ` j )
                           )
                         )
                     )
                   )
                 \/
                 E. T
                   (
                     T C_ I
                     /\
                     (
                       s < ( # ` T )
                       /\
                       A. i e. T A. j e. T
                         (
                           (
                             <. i , j >. e. Q
                             /\
                             i =/= j
                           )
                           ->
                           (
                             <. ( f ` j ) , ( f ` i ) >. e. R
                             /\
                             ( f ` j ) =/= ( f ` i )
                           )
                         )
                     )
                   )
               )
             )
  $.
$}
