$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2024_b4: the limiting normalized expectation of an integer-valued
  random walk that moves one step toward each independent uniform draw from
  1 through n is (1 - exp(-2)) / 2. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P24B4Uniform P Y n says that Y is an integer-valued random variable on the
  probability space P, takes values in 1 ... n, and assigns probability 1/n
  to every such value. This is exactly the uniform law on that finite set.

  P24B4Independent P M expands mutual independence of the entire family
  indexed by NN0 X. NN0 into measurability of every Borel preimage and the
  finite-family product identity. Currying and uncurrying identify this M
  with the source array m without changing any quantifier.

  P24B4Expectation P Y is set.mm's real Bochner integral when Y is integrable
  and zero otherwise, matching Lean's totalized integral. For positive n the
  initial condition, recurrence, and uniformity assumptions make A(n,n)
  bounded and measurable, so this value is its ordinary expectation.

  The final assertion retains arbitrary integer-valued arrays M and A on an
  arbitrary probability space, all positive n and nonnegative k, the exact
  pointwise three-case recurrence, and the limit along NN0. All declarations
  are unproved $a statement encodings; this database contains no $p proof
  declaration.
$)

$c P24B4Uniform P24B4Independent P24B4Expectation $.

p24b4-uniform-syntax $a wff ( P24B4Uniform P Y n ) $.
p24b4-independent-syntax $a wff ( P24B4Independent P M ) $.
p24b4-expectation-syntax $a class ( P24B4Expectation P Y ) $.

${
  $d P Y j n w $.

  p24b4-uniform-definition $a |- (
    ( P24B4Uniform P Y n )
    <->
    (
      n e. NN
      /\
      (
        Y : U. dom P --> ZZ
        /\
        (
          Y e. ( dom P MblFnM BrSiga )
          /\
          (
            A. w e. U. dom P ( Y ` w ) e. ( 1 ... n )
            /\
            A. j e. ( 1 ... n )
              ( P ` ( `' Y " { j } ) ) = ( 1 / n )
          )
        )
      )
    )
  ) $.
$}

${
  $d M P b f q s $.

  p24b4-independent-definition $a |- (
    ( P24B4Independent P M )
    <->
    (
      A. q e. ( NN0 X. NN0 ) A. b e. BrSiga
        ( `' ( M ` q ) " b ) e. dom P
      /\
      A. s e. ( Fin i^i ~P ( NN0 X. NN0 ) )
        A. f e. ( BrSiga ^m s )
          (
            P
            `
            (
              U. dom P
              i^i
              |^|_ q e. s
                ( `' ( M ` q ) " ( f ` q ) )
            )
          )
          =
          prod_ q e. s
            ( P ` ( `' ( M ` q ) " ( f ` q ) ) )
    )
  ) $.
$}

${
  $d P Y $.

  p24b4-expectation-definition $a |- (
    P24B4Expectation P Y
    =
    if
    (
      Y e. dom ( RRfld itgm P ) ,
      ( ( RRfld itgm P ) ` Y ) ,
      0
    )
  ) $.
$}

${
  $d A M P k n w $.

  putnambench-putnam-2024-b4 $a |-
    A. P e. Prob
      A. M e.
        ( ( ZZ ^m U. dom P ) ^m ( NN0 X. NN0 ) )
        A. A e.
          ( ( ZZ ^m U. dom P ) ^m ( NN0 X. NN0 ) )
          (
            (
              (
                A. n e. NN A. k e. NN0
                  ( P24B4Uniform P ( M ` <. n , k >. ) n )
                /\
                ( P24B4Independent P M )
              )
              /\
              (
                A. n e. NN A. w e. U. dom P
                  ( ( A ` <. n , 0 >. ) ` w ) = 1
                /\
                A. n e. NN A. k e. NN0 A. w e. U. dom P
                  (
                    ( ( A ` <. n , ( k + 1 ) >. ) ` w )
                    =
                    if
                    (
                      ( ( A ` <. n , k >. ) ` w )
                      <
                      ( ( M ` <. n , k >. ) ` w ) ,
                      ( ( A ` <. n , k >. ) ` w ) + 1 ,
                      if
                      (
                        ( ( A ` <. n , k >. ) ` w )
                        =
                        ( ( M ` <. n , k >. ) ` w ) ,
                        ( ( A ` <. n , k >. ) ` w ) ,
                        ( ( A ` <. n , k >. ) ` w ) - 1
                      )
                    )
                  )
              )
            )
            ->
            (
              n e. NN0 |->
                (
                  ( P24B4Expectation P ( A ` <. n , n >. ) )
                  /
                  n
                )
            )
            ~~>
            (
              ( 1 - ( exp ` ( -u 2 ) ) )
              /
              2
            )
          )
  $.
$}
