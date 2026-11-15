$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2010_a5: a group embedded in real three-space whose pairwise cross
  products are always either the embedded group product or zero has all
  pairwise cross products zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P10A5R3 is the full space of real-valued functions on the three-element
  interval 0 ... 2, P10A5Zero is its zero vector, and P10A5Cross is the
  ordinary coordinate cross product. In SetMM, g e. Grp supplies an arbitrary
  group, Base ` g is its carrier, and +g ` g is its operation.

  The map i ranges over all injections of the group carrier into real
  three-space, exactly representing the source embedding. The hypothesis
  and conclusion quantify over every pair of carrier elements, and the
  group product is compared only after applying i. All declarations are
  unproved $a statement encodings; this database contains no $p proof.
$)

$c P10A5R3 P10A5Zero P10A5Cross $.

p10a5-space-syntax $a class P10A5R3 $.
p10a5-zero-syntax $a class P10A5Zero $.
p10a5-cross-syntax $a class ( P10A5Cross A B ) $.

p10a5-space-definition $a |- P10A5R3 = ( RR ^m ( 0 ... 2 ) ) $.

${
  p10a5-zero-definition $a |- P10A5Zero =
    ( k e. ( 0 ... 2 ) |-> 0 )
  $.
$}

${
  $d A B k $.

  p10a5-cross-definition $a |- (
    P10A5Cross A B
  ) = (
    k e. ( 0 ... 2 ) |->
      if (
        k = 0 ,
        (
          ( ( A ` 1 ) x. ( B ` 2 ) )
          -
          ( ( A ` 2 ) x. ( B ` 1 ) )
        ) ,
        if (
          k = 1 ,
          (
            ( ( A ` 2 ) x. ( B ` 0 ) )
            -
            ( ( A ` 0 ) x. ( B ` 2 ) )
          ) ,
          (
            ( ( A ` 0 ) x. ( B ` 1 ) )
            -
            ( ( A ` 1 ) x. ( B ` 0 ) )
          )
        )
      )
  ) $.
$}

${
  $d a b g i $.

  putnambench-putnam-2010-a5 $a |- A. g A. i
    (
      (
        g e. Grp
        /\
        i : ( Base ` g ) -1-1-> P10A5R3
      )
      ->
      (
        A. a e. ( Base ` g )
          A. b e. ( Base ` g )
            (
              ( P10A5Cross ( i ` a ) ( i ` b ) )
              =
              (
                i
                `
                ( a ( +g ` g ) b )
              )
              \/
              ( P10A5Cross ( i ` a ) ( i ` b ) ) = P10A5Zero
            )
        ->
        A. a e. ( Base ` g )
          A. b e. ( Base ` g )
            ( P10A5Cross ( i ` a ) ( i ` b ) ) = P10A5Zero
      )
    )
  $.
$}
