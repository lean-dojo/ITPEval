$(
  Statement-only formalization of "The Solution of a Cubic" from Hundred
  Theorems item 037: Cardano's two-case characterization of all complex roots
  of a general cubic equation. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The imported set.mm database supplies the standard complex numbers CC,
  complex arithmetic, natural-number powers, equality, logical connectives,
  and restricted universal quantifiers.

  The condition w ^ 3 = 1 and w =/= 1 says that w is a primitive cube root of
  unity over CC. In the first assertion, p and q are the depressed-cubic
  coefficients, p is nonzero, r is a square root of q^2 + p^3, s is a cube
  root of q + r, and t*s = p. The conclusion characterizes exactly the three
  roots of the original cubic.

  The second assertion is the complementary case p = 0, written as
  3*a*c - b^2 = 0. A cube root s of 2*q gives the three roots after the same
  translation. Both declarations are unproved $a statements and add no proof
  to set.mm.
$)

hundred-theorems-037-cardano-nonzero-p $a
  |- A. a e. CC A. b e. CC A. c e. CC A. d e. CC
       A. p e. CC A. q e. CC A. r e. CC A. s e. CC
       A. t e. CC A. w e. CC A. x e. CC
       (
         (
           a =/= 0
           /\
           (
             ( w ^ 3 ) = 1
             /\
             (
               w =/= 1
               /\
               (
                 p =
                 (
                   (
                     ( ( 3 x. a ) x. c )
                     -
                     ( b ^ 2 )
                   )
                   /
                   ( 9 x. ( a ^ 2 ) )
                 )
                 /\
                 (
                   p =/= 0
                   /\
                   (
                     q =
                     (
                       (
                         (
                           ( ( ( 9 x. a ) x. b ) x. c )
                           -
                           ( 2 x. ( b ^ 3 ) )
                         )
                         -
                         ( ( 3 ^ 3 ) x. ( ( a ^ 2 ) x. d ) )
                       )
                       /
                       ( ( 2 x. ( 3 ^ 3 ) ) x. ( a ^ 3 ) )
                     )
                     /\
                     (
                       ( r ^ 2 ) =
                       (
                         ( q ^ 2 )
                         +
                         ( p ^ 3 )
                       )
                       /\
                       (
                         ( s ^ 3 ) = ( q + r )
                         /\
                         ( t x. s ) = p
                       )
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
                 ( a x. ( x ^ 3 ) )
                 +
                 ( b x. ( x ^ 2 ) )
               )
               +
               ( c x. x )
             )
             +
             d
           )
           =
           0
           <->
           (
             x =
             (
               (
                 s
                 -
                 t
               )
               -
               ( b / ( 3 x. a ) )
             )
             \/
             x =
             (
               (
                 ( s x. w )
                 -
                 ( t x. ( w ^ 2 ) )
               )
               -
               ( b / ( 3 x. a ) )
             )
             \/
             x =
             (
               (
                 ( s x. ( w ^ 2 ) )
                 -
                 ( t x. w )
               )
               -
               ( b / ( 3 x. a ) )
             )
           )
         )
       )
$.

hundred-theorems-037-cardano-zero-p $a
  |- A. a e. CC A. b e. CC A. c e. CC A. d e. CC
       A. q e. CC A. s e. CC A. w e. CC A. x e. CC
       (
         (
           a =/= 0
           /\
           (
             ( w ^ 3 ) = 1
             /\
             (
               w =/= 1
               /\
               (
                 (
                   (
                     ( 3 x. a )
                     x.
                     c
                   )
                   -
                   ( b ^ 2 )
                 )
                 =
                 0
                 /\
                 (
                   q =
                   (
                     (
                       (
                         ( ( ( 9 x. a ) x. b ) x. c )
                         -
                         ( 2 x. ( b ^ 3 ) )
                       )
                       -
                       ( ( 3 ^ 3 ) x. ( ( a ^ 2 ) x. d ) )
                     )
                     /
                     ( ( 2 x. ( 3 ^ 3 ) ) x. ( a ^ 3 ) )
                   )
                   /\
                   ( s ^ 3 ) = ( 2 x. q )
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
                 ( a x. ( x ^ 3 ) )
                 +
                 ( b x. ( x ^ 2 ) )
               )
               +
               ( c x. x )
             )
             +
             d
           )
           =
           0
           <->
           (
             x =
             (
               s
               -
               ( b / ( 3 x. a ) )
             )
             \/
             x =
             (
               ( s x. w )
               -
               ( b / ( 3 x. a ) )
             )
             \/
             x =
             (
               ( s x. ( w ^ 2 ) )
               -
               ( b / ( 3 x. a ) )
             )
           )
         )
       )
$.
