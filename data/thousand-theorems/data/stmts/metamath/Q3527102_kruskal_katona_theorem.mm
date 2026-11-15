$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3527102
  (thousand-theorems__metamath__Q3527102), "Kruskal&ndash;Katona theorem":
  among
  r-uniform families of subsets of an n-element ordered set, an initial
  segment of colex order has no larger lower shadow than any family of at
  least the same cardinality. This root artifact file contains no proof.
$)

$[ lib/set.mm $]

$(
  The finite ordered type Fin n is represented by SetMM's canonical finite
  ordinal 0 ..^ n. Q3527102ColexLe A B says that A precedes or equals B in
  colex order: when they differ, the greatest element at which membership
  differs belongs to B.

  Q3527102Shadow n F is the lower shadow of F, consisting of the subsets
  obtained by deleting one element from a member of F. Q3527102IsInitSeg
  states both r-uniformity and downward closure among all r-element subsets
  of 0 ..^ n in colex order.

  The final declaration is the single unproved corpus $a statement. All
  preceding local $a declarations are syntax or faithful definitions. This
  root artifact declares no local $p statement; imported lib/set.mm contains
  its standard library proofs.
$)

$c Q3527102ColexLe Q3527102Shadow Q3527102IsInitSeg $.

q3527102-colex-le-syntax $a
  wff ( Q3527102ColexLe A B ) $.
q3527102-shadow-syntax $a
  class ( Q3527102Shadow n F ) $.
q3527102-is-init-seg-syntax $a
  wff ( Q3527102IsInitSeg n r C ) $.

${
  $d A B j k $.

  q3527102-colex-le-definition $a |- (
    ( Q3527102ColexLe A B )
    <->
    (
      A = B
      \/
      E. k e. B
        (
          -. k e. A
          /\
          A. j e. NN0
            (
              k < j
              ->
              ( j e. A <-> j e. B )
            )
        )
    )
  ) $.
$}

${
  $d F n s t $.

  q3527102-shadow-definition $a |- (
    Q3527102Shadow n F
  ) = {
    s e. ~P ( 0 ..^ n ) |
    E. t e. F
      (
        s C_ t
        /\
        ( ( # ` s ) + 1 ) = ( # ` t )
      )
  } $.
$}

${
  $d C a b n r $.

  q3527102-is-init-seg-definition $a |- (
    ( Q3527102IsInitSeg n r C )
    <->
    (
      C C_ ~P ( 0 ..^ n )
      /\
      (
        A. a e. C ( # ` a ) = r
        /\
        A. a e. C
          A. b e. ~P ( 0 ..^ n )
            (
              (
                ( ( # ` b ) = r )
                /\
                ( Q3527102ColexLe b a )
              )
              ->
              b e. C
            )
      )
    )
  ) $.
$}

${
  $d a c n r s $.

  thousand-theorems-q3527102-kruskal-katona $a |-
    A. n e. NN0
      A. r e. NN0
        A. a e. Fin
          A. c e. Fin
            (
              (
                (
                  a C_ ~P ( 0 ..^ n )
                  /\
                  A. s e. a ( # ` s ) = r
                )
                /\
                (
                  ( # ` c ) <_ ( # ` a )
                  /\
                  ( Q3527102IsInitSeg n r c )
                )
              )
              ->
              (
                ( # ` ( Q3527102Shadow n c ) )
                <_
                ( # ` ( Q3527102Shadow n a ) )
              )
            )
  $.
$}
