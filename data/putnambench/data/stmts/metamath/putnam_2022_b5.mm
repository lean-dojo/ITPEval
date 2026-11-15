$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2022_b5: the zero value has maximal probability for every
  integer linear combination of independent random variables taking
  values -1, 0, and 1 exactly when 0 <= p <= 1/4. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, the carrier 1 ... n is an n-element set and is
  bijective with the source type Fin n. Thus ZZ ^m ( 1 ... n ) contains
  exactly the integer coefficient families, while
  { -u 1 , 0 , 1 } ^m ( 1 ... n ) contains exactly the possible
  outcomes X.

  Each displayed finite sum is the probability of
  sum_i a_i X_i = b: its summands are the product probabilities p for
  coordinates equal to 1 or -1 and 1 - 2p for coordinates equal to 0.
  Inlining the source's definitionally constrained Xset, Xprob, and P
  therefore preserves its proposition. The right side inlines the
  intended solution set, the closed real interval from 0 to 1/4.

  The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d X a b i n p $.

  putnambench-putnam-2022-b5 $a |- A. p e. RR
    (
      (
        (
          0 <_ p
          /\
          p <_ ( 1 / 2 )
        )
        /\
        A. n e. NN
          A. b e. ZZ
            A. a e. ( ZZ ^m ( 1 ... n ) )
              (
                sum_ X e.
                  {
                    X e.
                      (
                        { -u 1 , 0 , 1 }
                        ^m
                        ( 1 ... n )
                      )
                    |
                    (
                      sum_ i e. ( 1 ... n )
                        ( ( a ` i ) x. ( X ` i ) )
                    )
                    =
                    b
                  }
                  (
                    prod_ i e. ( 1 ... n )
                      if
                      (
                        (
                          ( X ` i ) = 1
                          \/
                          ( X ` i ) = -u 1
                        ) ,
                        p ,
                        ( 1 - ( 2 x. p ) )
                      )
                  )
                <_
                sum_ X e.
                  {
                    X e.
                      (
                        { -u 1 , 0 , 1 }
                        ^m
                        ( 1 ... n )
                      )
                    |
                    (
                      sum_ i e. ( 1 ... n )
                        ( ( a ` i ) x. ( X ` i ) )
                    )
                    =
                    0
                  }
                  (
                    prod_ i e. ( 1 ... n )
                      if
                      (
                        (
                          ( X ` i ) = 1
                          \/
                          ( X ` i ) = -u 1
                        ) ,
                        p ,
                        ( 1 - ( 2 x. p ) )
                      )
                  )
              )
      )
      <->
      p e. ( 0 [,] ( 1 / 4 ) )
    )
  $.
$}
