$(
  Statement-only formalization of Thousand Theorems corpus artifact Q226014
  (thousand-theorems__metamath__Q226014), "Poincare recurrence theorem": for
  a conservative measurable self-map of an arbitrary measure space, almost
  every point lying in a null-measurable set returns to that set at
  arbitrarily large natural iterates. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q226014Measure evaluates the outer measure induced by M, retaining arbitrary
  subsets of the carrier. Q226014NullMeasurable says that a set agrees with a
  measurable set up to an outer-null symmetric difference.

  Q226014Iterates is the unique NN0-indexed sequence beginning at x and
  repeatedly applying F. Q226014Conservative expands the source structure:
  F is measurable and nonsingular, and every measurable set of nonzero
  measure contains a point returning to it under a positive iterate.
  Q226014Frequently expands frequent membership along the natural-number
  atTop filter as membership at some index beyond every prescribed index.

  All declarations below are syntax, bidirectional definitions, or the final
  unproved $a statement. There are no $p declarations in this file.
$)

$c Q226014Measure Q226014NullMeasurable Q226014Iterates
   Q226014Conservative Q226014Frequently $.

q226014-measure-syntax
  $a class ( Q226014Measure M A ) $.
q226014-null-measurable-syntax
  $a wff ( Q226014NullMeasurable M S ) $.
q226014-iterates-syntax
  $a class ( Q226014Iterates M F x ) $.
q226014-conservative-syntax
  $a wff ( Q226014Conservative M F ) $.
q226014-frequently-syntax
  $a wff ( Q226014Frequently M F S x ) $.

${
  $d A M $.

  q226014-measure-definition $a |- (
    Q226014Measure M A
  ) =
    ( ( toOMeas ` M ) ` A )
  $.
$}

${
  $d M S T $.

  q226014-null-measurable-definition $a |- (
    ( Q226014NullMeasurable M S )
    <->
    E. T e. dom M
      (
        Q226014Measure
        M
        ( ( S \ T ) u. ( T \ S ) )
      ) = 0
  ) $.
$}

${
  $d F G M n x $.

  q226014-iterates-definition $a |- (
    Q226014Iterates M F x
  ) =
    (
      iota_ G e. ( ( U. dom M ) ^m NN0 )
        (
          ( G ` 0 ) = x
          /\
          A. n e. NN0
            ( G ` ( n + 1 ) ) = ( F ` ( G ` n ) )
        )
    )
  $.
$}

${
  $d A F M n x $.

  q226014-conservative-definition $a |- (
    ( Q226014Conservative M F )
    <->
    (
      F e. ( dom M MblFnM dom M )
      /\
      (
        A. A e. ~P ( U. dom M )
          (
            ( Q226014Measure M A ) = 0
            ->
            (
              Q226014Measure
              M
              ( `' F " A )
            ) = 0
          )
        /\
        A. A e. dom M
          (
            ( Q226014Measure M A ) =/= 0
            ->
            E. x e. A
              E. n e. NN
                ( ( Q226014Iterates M F x ) ` n ) e. A
          )
      )
    )
  ) $.
$}

${
  $d F M N S n x $.

  q226014-frequently-definition $a |- (
    ( Q226014Frequently M F S x )
    <->
    A. N e. NN0
      E. n e. NN0
        (
          N <_ n
          /\
          ( ( Q226014Iterates M F x ) ` n ) e. S
        )
  ) $.
$}

${
  $d A F G M N S T n x $.

  thousand-theorems-q226014-poincare-recurrence $a |-
    A. M e. U. ran measures
      A. F e. ( ( U. dom M ) ^m ( U. dom M ) )
        A. S e. ~P ( U. dom M )
          (
            (
              ( Q226014Conservative M F )
              /\
              ( Q226014NullMeasurable M S )
            )
            ->
            (
              Q226014Measure
              M
              {
                x e. S |
                  -. ( Q226014Frequently M F S x )
              }
            ) = 0
          )
  $.
$}
