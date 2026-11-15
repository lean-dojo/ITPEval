$(
  Statement-only formalization of "Liouville's Theorem and the Construction of
  Transcendental Numbers" from Hundred Theorems item 018: Liouville's
  approximation bound, transcendence of Liouville numbers, and the factorial
  series construction including the base-ten Liouville constant. This file
  contains no proof.
$)

$[ library/set.mm $]

$(
  Every mathematical symbol below is grounded in the imported set.mm
  database. RR, ZZ, NN, and NN0 are the standard real, integer, positive
  integer, and nonnegative-integer classes. AA is the set of complex
  algebraic numbers, defined in set.mm as the roots of nonzero integer
  polynomials. Thus a real number outside AA is transcendental.

  The first assertion is Liouville's inverse-power lower bound for irrational
  algebraic reals. The second states directly that a real admitting distinct
  rational approximations of every inverse-power order is transcendental.

  In the first construction assertion, p is an arbitrary integer-valued
  sequence, q is an integer base greater than one, and every digit p(k) lies
  in [0,q). Under just these bounds, the grounded infinite sum

    sum_ k e. NN0 ( ( p ` k ) / ( q ^ ( ! ` ( k + 1 ) ) ) )

  is asserted to be real, which by the set.mm definition means that the
  corresponding partial sums converge. The next assertion additionally
  assumes that nonzero digits occur at arbitrarily large indices and concludes
  the Liouville approximation property and transcendence. The final assertion
  covers both source indexings of the base-ten constant and states their exact
  difference of 1/10. All five declarations are unproved $a statements.
$)

${
  $d A a $.
  $d A b $.
  $d A c $.
  $d A n $.

  hundred-theorems-018-liouville-lower-bound $a
    |- (
         A e. RR
         ->
         (
           ( A e. AA /\ A e/ QQ )
           ->
           E. n e. NN E. c e. RR+
             A. a e. ZZ A. b e. NN
               ( ( c / ( b ^ n ) ) <
                 ( abs ` ( A - ( a / b ) ) ) )
         )
       )
  $.
$}

${
  $d A a $.
  $d A b $.
  $d A n $.

  hundred-theorems-018-liouville-transcendental $a
    |- (
         A e. RR
         ->
         (
           (
             A. n e. NN0
               E. a e. ZZ E. b e. ZZ
                 (
                   ( 1 < b /\ A =/= ( a / b ) )
                   /\
                   (
                     ( abs ` ( A - ( a / b ) ) )
                     <
                     ( 1 / ( b ^ n ) )
                   )
                 )
           )
           ->
           A e/ AA
         )
       )
  $.
$}

${
  $d p k $.
  $d q k $.

  hundred-theorems-018-standard-liouville-convergence $a
    |- A. p A. q
         (
           (
             ( p : NN0 --> ZZ /\ q e. ZZ )
             /\
             (
               1 < q
               /\
               A. k e. NN0
                 ( 0 <_ ( p ` k ) /\ ( p ` k ) < q )
             )
           )
           ->
           sum_ k e. NN0
             ( ( p ` k ) / ( q ^ ( ! ` ( k + 1 ) ) ) )
             e. RR
         )
  $.
$}

${
  $d a k $.
  $d a n $.
  $d b k $.
  $d b n $.
  $d k n $.
  $d p a $.
  $d p b $.
  $d p k $.
  $d p n $.
  $d q a $.
  $d q b $.
  $d q k $.
  $d q n $.

  hundred-theorems-018-standard-liouville-construction $a
    |- A. p A. q
         (
           (
             ( p : NN0 --> ZZ /\ q e. ZZ )
             /\
             (
               (
                 1 < q
                 /\
                 A. k e. NN0
                   ( 0 <_ ( p ` k ) /\ ( p ` k ) < q )
               )
               /\
               A. n e. NN0 E. k e. NN0
                 ( n <_ k /\ ( p ` k ) =/= 0 )
             )
           )
           ->
           (
             (
               A. n e. NN0
                 E. a e. ZZ E. b e. ZZ
                   (
                     (
                       1 < b
                       /\
                       sum_ k e. NN0
                         ( ( p ` k ) / ( q ^ ( ! ` ( k + 1 ) ) ) )
                         =/= ( a / b )
                     )
                     /\
                     (
                       (
                         abs ` (
                           ( sum_ k e. NN0
                               ( ( p ` k ) /
                                 ( q ^ ( ! ` ( k + 1 ) ) ) ) )
                           - ( a / b )
                         )
                       )
                       <
                       ( 1 / ( b ^ n ) )
                     )
                   )
             )
             /\
             sum_ k e. NN0
               ( ( p ` k ) / ( q ^ ( ! ` ( k + 1 ) ) ) )
               e/ AA
           )
         )
  $.
$}

${
  $d k j $.

  hundred-theorems-018-liouville-constant $a
    |- (
         (
           sum_ k e. NN0
             ( 1 / ( ; 1 0 ^ ( ! ` ( k + 1 ) ) ) )
           e. RR
           /\
           sum_ k e. NN0
             ( 1 / ( ; 1 0 ^ ( ! ` ( k + 1 ) ) ) )
           e/ AA
         )
         /\
         (
           (
             sum_ j e. NN0
               ( 1 / ( ; 1 0 ^ ( ! ` j ) ) )
           )
           =
           (
             ( 1 / ; 1 0 )
             +
             sum_ k e. NN0
               ( 1 / ( ; 1 0 ^ ( ! ` ( k + 1 ) ) ) )
           )
           /\
           (
             sum_ j e. NN0
               ( 1 / ( ; 1 0 ^ ( ! ` j ) ) )
             e. RR
             /\
             sum_ j e. NN0
               ( 1 / ( ; 1 0 ^ ( ! ` j ) ) )
             e/ AA
           )
         )
       )
  $.
$}
