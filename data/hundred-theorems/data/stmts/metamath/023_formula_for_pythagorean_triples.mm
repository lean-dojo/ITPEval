$(
  Statement-only formalization of "Formula for Pythagorean Triples" from Hundred Theorems item
  023: the general integer classification and its normalized nonnegative form. This file contains
  no proof.
$)

$[ library/set.mm $]

$(
  The imported set.mm database supplies the standard integers ZZ, arithmetic,
  order, gcd, and the classes Even and Odd. The first assertion classifies all
  integer solutions, with either ordering of the legs and either sign of the
  hypotenuse. The second records the equivalent normalized classification for
  nonnegative triples, including ordered coprime opposite-parity parameters
  and a nonnegative scale. Both declarations are unproved $a statements.
$)

${
  $d x y z k m n $.

  hundred-theorems-023-pythagorean-triples-general $a
    |- A. x e. ZZ A. y e. ZZ A. z e. ZZ
         (
           ( ( ( x ^ 2 ) + ( y ^ 2 ) ) = ( z ^ 2 ) )
           <->
           E. k e. ZZ E. m e. ZZ E. n e. ZZ
             (
               (
                 (
                   x = ( k x. ( ( m ^ 2 ) - ( n ^ 2 ) ) )
                   /\
                   y = ( k x. ( ( 2 x. m ) x. n ) )
                 )
                 \/
                 (
                   x = ( k x. ( ( 2 x. m ) x. n ) )
                   /\
                   y = ( k x. ( ( m ^ 2 ) - ( n ^ 2 ) ) )
                 )
               )
               /\
               (
                 z = ( k x. ( ( m ^ 2 ) + ( n ^ 2 ) ) )
                 \/
                 z = ( -u k x. ( ( m ^ 2 ) + ( n ^ 2 ) ) )
               )
             )
         )
  $.
$}

${
  $d x y z p q r $.

  hundred-theorems-023-pythagorean-triples-nonnegative $a
    |- A. x e. ZZ A. y e. ZZ A. z e. ZZ
         (
           (
             0 <_ x
             /\
             (
               0 <_ y
               /\
               (
                 0 <_ z
                 /\
                 ( ( x ^ 2 ) + ( y ^ 2 ) ) = ( z ^ 2 )
               )
             )
           )
           <->
           E. p e. ZZ E. q e. ZZ E. r e. ZZ
             (
               (
                 (
                   x = ( r x. ( ( q ^ 2 ) - ( p ^ 2 ) ) )
                   /\
                   y = ( ( 2 x. r ) x. ( p x. q ) )
                 )
                 \/
                 (
                   x = ( ( 2 x. r ) x. ( p x. q ) )
                   /\
                   y = ( r x. ( ( q ^ 2 ) - ( p ^ 2 ) ) )
                 )
               )
               /\
               (
                 z = ( r x. ( ( p ^ 2 ) + ( q ^ 2 ) ) )
                 /\
                 (
                   0 <_ r
                   /\
                   (
                     0 <_ p
                     /\
                     (
                       0 < q
                       /\
                       (
                         p <_ q
                         /\
                         (
                           ( p gcd q ) = 1
                           /\
                           (
                             ( p e. Even /\ q e. Odd )
                             \/
                             ( p e. Odd /\ q e. Even )
                           )
                         )
                       )
                     )
                   )
                 )
               )
             )
         )
  $.
$}
