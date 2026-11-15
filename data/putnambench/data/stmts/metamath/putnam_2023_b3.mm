$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2023_b3: the expected length of the longest zigzag subsequence of
  independent uniform real samples from the closed unit interval is
  (2n + 2) / 3 for n at least two. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P23B3Index(n) is the canonical n-element index set 0 ..^ n, and
  P23B3Cube(n) is the full n-dimensional closed unit cube. Product Lebesgue
  measure voln on this finite coordinate space is the joint law of n
  independent uniform samples on [0,1].

  P23B3ZigZag(Y,k) states exactly that the nonempty k-term real sequence Y
  has either one term, or has nonzero successive differences whose signs
  alternate. P23B3Subsequence(X,n,k) keeps the increasing index map
  existentially quantified and says that it selects a k-term zigzag
  subsequence of X. P23B3Length(X,n) is the supremum in NN0 of all such
  positive lengths; for n at least two this nonempty bounded set has the
  same greatest element specified by IsGreatest in the Lean source.

  P23B3Integrand(n) extends this length by zero off the unit cube, so its
  real Bochner integral against voln is the required expectation. Every
  declaration below is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

$c P23B3Index P23B3Cube P23B3ZigZag $.
$c P23B3Subsequence P23B3Length P23B3Integrand $.

p23b3-index-syntax $a class ( P23B3Index n ) $.
p23b3-cube-syntax $a class ( P23B3Cube n ) $.
p23b3-zigzag-syntax $a wff ( P23B3ZigZag Y k ) $.
p23b3-subsequence-syntax $a wff ( P23B3Subsequence X n k ) $.
p23b3-length-syntax $a class ( P23B3Length X n ) $.
p23b3-integrand-syntax $a class ( P23B3Integrand n ) $.

p23b3-index-definition $a |- (
  P23B3Index n
) = (
  0 ..^ n
) $.

${
  $d X i n $.

  p23b3-cube-definition $a |- (
    P23B3Cube n
  ) = {
    X e. ( RR ^m ( P23B3Index n ) ) |
      A. i e. ( P23B3Index n )
        (
          0 <_ ( X ` i )
          /\
          ( X ` i ) <_ 1
        )
  } $.
$}

${
  $d Y i k $.

  p23b3-zigzag-definition $a |- (
    ( P23B3ZigZag Y k )
    <->
    (
      (
        k e. NN
        /\
        Y : ( P23B3Index k ) --> RR
      )
      /\
      (
        k = 1
        \/
        (
          A. i e. ( P23B3Index k )
            (
              ( i + 1 ) < k
              ->
              ( Y ` ( i + 1 ) ) =/= ( Y ` i )
            )
          /\
          A. i e. ( P23B3Index k )
            (
              ( i + 2 ) < k
              ->
              (
                ( Y ` ( i + 2 ) ) < ( Y ` ( i + 1 ) )
                <->
                ( Y ` i ) < ( Y ` ( i + 1 ) )
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d I X i j k n $.

  p23b3-subsequence-definition $a |- (
    ( P23B3Subsequence X n k )
    <->
    (
      (
        k e. NN
        /\
        k <_ n
      )
      /\
      E. I
        (
          I : ( P23B3Index k ) --> ( P23B3Index n )
          /\
          (
            A. i e. ( P23B3Index k )
              A. j e. ( P23B3Index k )
                (
                  i < j
                  ->
                  ( I ` i ) < ( I ` j )
                )
            /\
            (
              P23B3ZigZag
                (
                  i e. ( P23B3Index k ) |->
                    ( X ` ( I ` i ) )
                )
                k
            )
          )
        )
    )
  ) $.
$}

${
  $d X k n $.

  p23b3-length-definition $a |- (
    P23B3Length X n
  ) = sup (
    {
      k e. NN |
        ( P23B3Subsequence X n k )
    } ,
    NN0 ,
    <
  ) $.
$}

${
  $d X n $.

  p23b3-integrand-definition $a |- (
    P23B3Integrand n
  ) = (
    X e. ( RR ^m ( P23B3Index n ) ) |->
      if (
        X e. ( P23B3Cube n ) ,
        ( P23B3Length X n ) ,
        0
      )
  ) $.
$}

putnambench-putnam-2023-b3 $a |- A. n e. NN
  (
    2 <_ n
    ->
    (
      (
        RRfld
        itgm
        ( voln ` ( P23B3Index n ) )
      )
      `
      ( P23B3Integrand n )
    )
    =
    (
      (
        ( 2 x. n )
        +
        2
      )
      /
      3
    )
  )
$.
