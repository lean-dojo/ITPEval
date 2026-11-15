$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1996_b3: for every integer n at least two, the largest cyclic
  adjacent-product sum over permutations of 1 through n has the stated
  cubic closed form. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier 0 ..^ n consists of the n indices 0 through n - 1, and
  1 ... n consists of the n values 1 through n. Thus a bijection x between
  these carriers is exactly a source sequence whose entries are a
  permutation of 1 through n. The summand at i multiplies x(i) by the next
  cyclic entry x((i+1) mod n).

  The first conjunct states that some permutation attains the displayed
  value. The second states that every permutation has cyclic sum at most
  that value. Together they are the source greatest-value assertion, with
  the annotated solution inlined. The final declaration is a single
  unproved $a corpus statement; this database contains no $p proof.
$)

${
  $d i n x $.

  putnambench-putnam-1996-b3 $a |- A. n e. NN
    (
      2 <_ n
      ->
      (
        E. x
          (
            x : ( 0 ..^ n ) -1-1-onto-> ( 1 ... n )
            /\
            (
              sum_ i e. ( 0 ..^ n )
                ( ( x ` i ) x. ( x ` ( ( i + 1 ) mod n ) ) )
            )
            =
            (
              (
                (
                  ( 2 x. ( n ^ 3 ) )
                  +
                  ( 3 x. ( n ^ 2 ) )
                )
                -
                ( ; 1 1 x. n )
              )
              +
              ; 1 8
            )
            /
            6
          )
        /\
        A. x
          (
            x : ( 0 ..^ n ) -1-1-onto-> ( 1 ... n )
            ->
            (
              sum_ i e. ( 0 ..^ n )
                ( ( x ` i ) x. ( x ` ( ( i + 1 ) mod n ) ) )
            )
            <_
            (
              (
                (
                  ( 2 x. ( n ^ 3 ) )
                  +
                  ( 3 x. ( n ^ 2 ) )
                )
                -
                ( ; 1 1 x. n )
              )
              +
              ; 1 8
            )
            /
            6
          )
      )
    )
  $.
$}
