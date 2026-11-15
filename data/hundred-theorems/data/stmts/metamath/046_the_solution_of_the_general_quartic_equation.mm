$(
  Statement-only formalization of "The Solution of the General Quartic
  Equation" from Hundred Theorems item 046: Ferrari's two-case
  characterization of all four complex roots of a quartic equation. This file
  contains no proof.
$)

$[ library/set.mm $]

$(
  The imported set.mm database supplies the standard complex numbers CC,
  complex arithmetic, natural-number powers, equality, logical connectives,
  and restricted universal quantifiers.

  The first assertion is Ferrari's nondegenerate case. The leading
  coefficient is nonzero, p, q, and r are the depressed-quartic coefficients,
  q is nonzero, u solves the cubic resolvent, and s, v, and w satisfy the
  auxiliary square equations. The conclusion characterizes exactly the four
  roots of the original quartic.

  The second assertion is the complementary case where the depressed linear
  coefficient is zero. The quartic becomes biquadratic after translation, and
  t, v, and w satisfy the corresponding square equations. Both declarations
  are unproved $a statements and add no proof to set.mm.
$)

hundred-theorems-046-ferrari-nonzero-q $a
  |- A. a e. CC A. b e. CC A. c e. CC A. d e. CC A. e e. CC
       A. p e. CC A. q e. CC A. r e. CC A. s e. CC A. u e. CC
       A. v e. CC A. w e. CC A. x e. CC
       (
         (
           a =/= 0
           /\
           (
             p =
             (
               (
                 ( ( 8 x. a ) x. c )
                 -
                 ( 3 x. ( b ^ 2 ) )
               )
               /
               ( 8 x. ( a ^ 2 ) )
             )
           )
           /\
           (
             q =
             (
               (
                 (
                   ( b ^ 3 )
                   -
                   ( 4 x. ( ( a x. b ) x. c ) )
                 )
                 +
                 ( 8 x. ( ( a ^ 2 ) x. d ) )
               )
               /
               ( 8 x. ( a ^ 3 ) )
             )
           )
           /\
           (
             q =/= 0
             /\
             (
               r =
               (
                 (
                   (
                     (
                       ( ( 2 ^ 4 ) x. ( ( a x. ( b ^ 2 ) ) x. c ) )
                       +
                       ( ( 2 ^ 8 ) x. ( ( a ^ 3 ) x. e ) )
                     )
                     -
                     ( 3 x. ( b ^ 4 ) )
                   )
                   -
                   ( ( 2 ^ 6 ) x. ( ( ( a ^ 2 ) x. b ) x. d ) )
                 )
                 /
                 ( ( 2 ^ 8 ) x. ( a ^ 4 ) )
               )
               /\
               (
                 (
                   (
                     (
                       (
                         ( u ^ 3 )
                         -
                         ( p x. ( u ^ 2 ) )
                       )
                       -
                       ( 4 x. ( r x. u ) )
                     )
                     +
                     ( 4 x. ( p x. r ) )
                   )
                   -
                   ( q ^ 2 )
                 )
                 =
                 0
                 /\
                 (
                   ( s ^ 2 ) = ( u - p )
                   /\
                   (
                     ( v ^ 2 ) =
                     (
                       ( 4 x. ( s ^ 2 ) )
                       -
                       ( 8 x. ( u - ( q / s ) ) )
                     )
                     /\
                     ( w ^ 2 ) =
                     (
                       ( 4 x. ( s ^ 2 ) )
                       -
                       ( 8 x. ( u + ( q / s ) ) )
                     )
                   )
                 )
               )
             )
           )
         )
         ->
         (
           (
             (
               (
                 (
                   ( a x. ( x ^ 4 ) )
                   +
                   ( b x. ( x ^ 3 ) )
                 )
                 +
                 ( c x. ( x ^ 2 ) )
               )
               +
               ( d x. x )
             )
             +
             e
           )
           =
           0
           <->
           (
             x =
             (
               (
                 (
                   ( 0 - ( 2 x. s ) )
                   -
                   v
                 )
                 /
                 4
               )
               -
               ( b / ( 4 x. a ) )
             )
             \/
             x =
             (
               (
                 (
                   ( 0 - ( 2 x. s ) )
                   +
                   v
                 )
                 /
                 4
               )
               -
               ( b / ( 4 x. a ) )
             )
             \/
             x =
             (
               (
                 (
                   ( 2 x. s )
                   -
                   w
                 )
                 /
                 4
               )
               -
               ( b / ( 4 x. a ) )
             )
             \/
             x =
             (
               (
                 (
                   ( 2 x. s )
                   +
                   w
                 )
                 /
                 4
               )
               -
               ( b / ( 4 x. a ) )
             )
           )
         )
       )
$.

hundred-theorems-046-ferrari-zero-q $a
  |- A. a e. CC A. b e. CC A. c e. CC A. d e. CC A. e e. CC
       A. p e. CC A. r e. CC A. t e. CC A. v e. CC A. w e. CC
       A. x e. CC
       (
         (
           a =/= 0
           /\
           (
             p =
             (
               (
                 ( ( 8 x. a ) x. c )
                 -
                 ( 3 x. ( b ^ 2 ) )
               )
               /
               ( 8 x. ( a ^ 2 ) )
             )
           )
           /\
           (
             (
               (
                 ( b ^ 3 )
                 -
                 ( 4 x. ( ( a x. b ) x. c ) )
               )
               +
               ( 8 x. ( ( a ^ 2 ) x. d ) )
             )
             =
             0
             /\
             (
               r =
               (
                 (
                   (
                     (
                       ( ( 2 ^ 4 ) x. ( ( a x. ( b ^ 2 ) ) x. c ) )
                       +
                       ( ( 2 ^ 8 ) x. ( ( a ^ 3 ) x. e ) )
                     )
                     -
                     ( 3 x. ( b ^ 4 ) )
                   )
                   -
                   ( ( 2 ^ 6 ) x. ( ( ( a ^ 2 ) x. b ) x. d ) )
                 )
                 /
                 ( ( 2 ^ 8 ) x. ( a ^ 4 ) )
               )
               /\
               (
                 ( t ^ 2 ) =
                 (
                   ( p ^ 2 )
                   -
                   ( 4 x. r )
                 )
                 /\
                 (
                   ( v ^ 2 ) =
                   (
                     (
                       ( 0 - p )
                       +
                       t
                     )
                     /
                     2
                   )
                   /\
                   ( w ^ 2 ) =
                   (
                     (
                       ( 0 - p )
                       -
                       t
                     )
                     /
                     2
                   )
                 )
               )
             )
           )
         )
         ->
         (
           (
             (
               (
                 (
                   ( a x. ( x ^ 4 ) )
                   +
                   ( b x. ( x ^ 3 ) )
                 )
                 +
                 ( c x. ( x ^ 2 ) )
               )
               +
               ( d x. x )
             )
             +
             e
           )
           =
           0
           <->
           (
             x =
             (
               v
               -
               ( b / ( 4 x. a ) )
             )
             \/
             x =
             (
               ( 0 - v )
               -
               ( b / ( 4 x. a ) )
             )
             \/
             x =
             (
               w
               -
               ( b / ( 4 x. a ) )
             )
             \/
             x =
             (
               ( 0 - w )
               -
               ( b / ( 4 x. a ) )
             )
           )
         )
       )
$.
