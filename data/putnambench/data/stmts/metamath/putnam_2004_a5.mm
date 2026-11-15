$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2004_a5: the expected number of connected monochromatic regions in
  a uniformly two-colored finite rectangular checkerboard is greater than
  one eighth of the number of squares. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P04A5Board M N is the canonical finite carrier
  (0 ..^ M) X. (0 ..^ N), which is exactly Fin M X. Fin N. P04A5Adj M N
  relates two squares precisely when they share a side.

  P04A5Conn M N C relates P and Q when a nonempty finite word of board
  squares starts at P, ends at Q, has one common C-color, and has adjacent
  successive squares. P04A5CMR M N C counts the subsets that are exactly
  these connected classes. Thus the source parameters adj, connected, and
  cmr, which are uniquely fixed by equality hypotheses, have been inlined.

  Restricting M and N to NN is equivalent to the source inhabitance
  assumption on Fin M X. Fin N. The two-element set { 0 , 1 } is a
  bijective relabeling of the source's two proposition-valued colors. The
  final inequality is the source coloring sum, equivalently its expectation
  after division by 2 ^ (M x. N).

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P04A5Board P04A5Adj P04A5Conn P04A5CMR $.

p04a5-board-syntax $a class ( P04A5Board A B ) $.
p04a5-adj-syntax $a class ( P04A5Adj A B ) $.
p04a5-conn-syntax $a class ( P04A5Conn A B C ) $.
p04a5-cmr-syntax $a class ( P04A5CMR A B C ) $.

p04a5-board-definition $a |- ( P04A5Board M N ) =
  ( ( 0 ..^ M ) X. ( 0 ..^ N ) )
$.

${
  $d M N z $.

  p04a5-adj-definition $a |- ( P04A5Adj M N ) = {
    z e. ( ( P04A5Board M N ) X. ( P04A5Board M N ) ) |
    (
      (
        ( 1st ` ( 1st ` z ) ) = ( 1st ` ( 2nd ` z ) )
        /\
        (
          (
            ( 2nd ` ( 1st ` z ) ) + 1
          )
          =
          ( 2nd ` ( 2nd ` z ) )
          \/
          (
            ( 2nd ` ( 2nd ` z ) ) + 1
          )
          =
          ( 2nd ` ( 1st ` z ) )
        )
      )
      \/
      (
        ( 2nd ` ( 1st ` z ) ) = ( 2nd ` ( 2nd ` z ) )
        /\
        (
          (
            ( 1st ` ( 1st ` z ) ) + 1
          )
          =
          ( 1st ` ( 2nd ` z ) )
          \/
          (
            ( 1st ` ( 2nd ` z ) ) + 1
          )
          =
          ( 1st ` ( 1st ` z ) )
        )
      )
    )
  } $.
$}

${
  $d C M N c i w z $.

  p04a5-conn-definition $a |- ( P04A5Conn M N C ) = {
    z e. ( ( P04A5Board M N ) X. ( P04A5Board M N ) ) |
    E. w e. ( Word ( P04A5Board M N ) \ { (/) } )
      (
        ( w ` 0 ) = ( 1st ` z )
        /\
        (
          ( w ` ( ( # ` w ) - 1 ) ) = ( 2nd ` z )
          /\
          (
            E. c e. { 0 , 1 }
              A. i e. ( 0 ..^ ( # ` w ) )
                ( C ` ( w ` i ) ) = c
            /\
            A. i e. ( 0 ..^ ( ( # ` w ) - 1 ) )
              <. ( w ` i ) , ( w ` ( i + 1 ) ) >.
                e. ( P04A5Adj M N )
          )
        )
      )
  } $.
$}

${
  $d C M N P Q R $.

  p04a5-cmr-definition $a |- ( P04A5CMR M N C ) = (
    #
    `
    {
      R e. ~P ( P04A5Board M N ) |
      E. P e. R
        A. Q e. ( P04A5Board M N )
          (
            Q e. R
            <->
            <. P , Q >. e. ( P04A5Conn M N C )
          )
    }
  ) $.
$}

${
  $d C m n $.

  putnambench-putnam-2004-a5 $a |- A. m e. NN A. n e. NN
    (
      (
        ( 2 ^ ( m x. n ) )
        x.
        ( ( m x. n ) / 8 )
      )
      <
      (
        sum_ C e. ( { 0 , 1 } ^m ( P04A5Board m n ) )
          ( P04A5CMR m n C )
      )
    )
  $.
$}
