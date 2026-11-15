$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2024_b5: for positive sequence lengths k and m, the number of pairs
  of nondecreasing positive-integer sequences whose final terms are at most a
  common z at most n agrees on positive n with a rational polynomial having
  nonnegative coefficients. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The half-open interval 0 ..^ q is set.mm's q-element representation of
  Fin q. A qualifying sequence is represented as a function from this
  interval to NN. This is equivalent to a natural-valued monotone function
  whose first value is at least one; for positive q, monotonicity then makes
  every value positive. Its last value is the value at q - 1.

  P24B5Count uses the nested ordered-pair representation
  <. <. x , y >. , z >. of the source triples. The bounded final values and
  monotonicity make the displayed set finite, so # is exactly Set.ncard here.
  P24B5QFld is set.mm's rational subfield of the complex field, and Poly1,
  eval1, and coe1 provide rational polynomials, evaluation, and coefficients.

  The final declaration retains the arbitrary natural-valued function f and
  its defining equality at every natural n. It is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

$c P24B5Count P24B5QFld $.

p24b5-count-syntax $a class ( P24B5Count A B C ) $.
p24b5-qfld-syntax $a class P24B5QFld $.

p24b5-qfld-definition $a |-
  P24B5QFld = ( CCfld |`s QQ ) $.

${
  $d i j t K $.
  $d i j t M $.
  $d i j t N $.

  p24b5-count-definition $a |- ( P24B5Count K M N ) =
    (
      # `
      {
        t e.
          (
            (
              ( NN ^m ( 0 ..^ K ) )
              X.
              ( NN ^m ( 0 ..^ M ) )
            )
            X.
            NN0
          )
        |
        (
          (
            A. i e. ( 0 ..^ K )
              A. j e. ( 0 ..^ K )
                (
                  i <_ j
                  ->
                  (
                    ( ( 1st ` ( 1st ` t ) ) ` i )
                    <_
                    ( ( 1st ` ( 1st ` t ) ) ` j )
                  )
                )
            /\
            (
              ( ( 1st ` ( 1st ` t ) ) ` ( K - 1 ) )
              <_
              ( 2nd ` t )
            )
          )
          /\
          (
            (
              A. i e. ( 0 ..^ M )
                A. j e. ( 0 ..^ M )
                  (
                    i <_ j
                    ->
                    (
                      ( ( 2nd ` ( 1st ` t ) ) ` i )
                      <_
                      ( ( 2nd ` ( 1st ` t ) ) ` j )
                    )
                  )
              /\
              (
                ( ( 2nd ` ( 1st ` t ) ) ` ( M - 1 ) )
                <_
                ( 2nd ` t )
              )
            )
            /\
            ( ( 2nd ` t ) <_ N )
          )
        )
      }
    ) $.
$}

${
  $d P f i k m n $.

  putnambench-putnam-2024-b5 $a |-
    A. k e. NN
      A. m e. NN
        A. f e. ( NN0 ^m NN0 )
          (
            A. n e. NN0
              ( f ` n ) = ( P24B5Count k m n )
            ->
            E. P e. ( Base ` ( Poly1 ` P24B5QFld ) )
              (
                A. n e. NN
                  (
                    ( f ` n )
                    =
                    ( ( ( eval1 ` P24B5QFld ) ` P ) ` n )
                  )
                /\
                A. i e. NN0
                  0 <_ ( ( coe1 ` P ) ` i )
              )
          )
  $.
$}
