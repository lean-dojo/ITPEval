$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1979_a1: the multiset consisting of one 2 and 659 copies of 3
  maximizes the product among nonempty finite multisets of positive natural
  numbers whose sum is 1979. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A nonempty finite multiset of positive natural numbers is represented by
  an enumeration a in NN ^m ( 1 ... n ), with n in NN. Passing between an
  enumeration and its multiset of values is bidirectional up to permutation,
  and finite cardinality, sum, and product are invariant under permutation.
  Thus the quantified families below range over exactly the source objects.

  P79A1Ten, P79A1N, and P79A1Total are the decimal values 10, 660, and 1979,
  written using set.mm's declared single-digit numerals. P79A1Sol is the
  canonical P79A1N-term enumeration with value 2 at index 1 and value 3 at
  every other index. The first conjunct states its source predicate, including
  positivity and sum P79A1Total; the second states maximality against every
  admissible multiset enumeration.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P79A1Ten P79A1N P79A1Total P79A1Sol $.

p79a1-ten-syntax $a class P79A1Ten $.
p79a1-size-syntax $a class P79A1N $.
p79a1-total-syntax $a class P79A1Total $.
p79a1-solution-syntax $a class P79A1Sol $.

p79a1-ten-definition $a |- P79A1Ten = ( 9 + 1 ) $.

p79a1-size-definition $a |- P79A1N =
  ( ( ( 6 x. P79A1Ten ) + 6 ) x. P79A1Ten ) $.

p79a1-total-definition $a |- P79A1Total =
  (
    (
      (
        (
          (
            ( 1 x. P79A1Ten )
            +
            9
          )
          x.
          P79A1Ten
        )
        +
        7
      )
      x.
      P79A1Ten
    )
    +
    9
  ) $.

p79a1-solution-definition $a |- P79A1Sol =
  (
    i e. ( 1 ... P79A1N ) |->
      if ( i = 1 , 2 , 3 )
  ) $.

${
  $d a i n $.

  putnambench-putnam-1979-a1 $a |- (
    (
      P79A1Sol e. ( NN ^m ( 1 ... P79A1N ) )
      /\
      (
        sum_ i e. ( 1 ... P79A1N )
          ( P79A1Sol ` i )
      )
      =
      P79A1Total
    )
    /\
    A. n e. NN
      A. a e. ( NN ^m ( 1 ... n ) )
        (
          (
            sum_ i e. ( 1 ... n )
              ( a ` i )
          )
          =
          P79A1Total
          ->
          (
            prod_ i e. ( 1 ... n )
              ( a ` i )
          )
          <_
          (
            prod_ i e. ( 1 ... P79A1N )
              ( P79A1Sol ` i )
          )
        )
  ) $.
$}
