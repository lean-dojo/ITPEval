$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_61 (verina__metamath__verina_advanced_61), catalog title
  productExceptSelf: exact prefix-product and reversed suffix-product folds
  compute, for every position of an arbitrary finite integer list, the
  product of all other entries, together with the complete correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set. The empty word (/) represents
  the empty list.

  VERINA61ComputePrefGraph is the exact source computepref fold trace. It
  starts with integer one and appends the previous last accumulator entry
  times the next input entry. VERINA61ReverseGraph is exact list reversal.
  VERINA61ComputeSuffixGraph first reverses the input, performs the same
  append-at-the-end product fold from one, and reverses that complete trace,
  exactly reproducing computeSuffix.

  VERINA61ResultGraph maps every input index i to prefix[i] times
  suffix[i+1]. VERINA61ProductExceptSelf preserves the source's explicit
  empty-input branch and otherwise selects the unique result of this graph.
  Thus the executable result is fixed independently of the postcondition,
  uses the same two linear product folds, and performs no division.

  VERINA61TakeGraph and VERINA61DropGraph reproduce List.take and List.drop
  for every natural count, including counts beyond the input length.
  VERINA61MyProdGraph is the exact recursive List.myprod computation: its
  trace has terminal value one and each preceding value is the current entry
  times the product of the remaining suffix.
  VERINA61Post has the source result-length equality and the complete
  List.range/List.all clause. Under that length equality every ranged lookup
  is in bounds, so the source option equality result[i]! = some(value) is
  bidirectionally equivalent to the displayed word-entry equality.

  VERINA61Pre is the source True precondition on typed List Int inputs. The
  proof-valued precondition argument is computationally and propositionally
  unused and is represented by the explicit antecedent of the final
  correctness assertion. Every earlier $a is syntax or a faithful definition,
  and this database has no $p declaration.
$)

$c
  VERINA61ComputePrefGraph VERINA61ComputePref
  VERINA61ReverseGraph
  VERINA61ComputeSuffixGraph VERINA61ComputeSuffix
  VERINA61ResultGraph
  VERINA61Pre VERINA61ProductExceptSelf
  VERINA61NatMin
  VERINA61TakeGraph VERINA61Take
  VERINA61DropGraph VERINA61Drop
  VERINA61MyProdGraph VERINA61MyProd
  VERINA61Post
$.

verina61-compute-pref-graph-syntax
  $a wff ( VERINA61ComputePrefGraph A B ) $.
verina61-compute-pref-syntax
  $a class ( VERINA61ComputePref A ) $.
verina61-reverse-graph-syntax
  $a wff ( VERINA61ReverseGraph A B ) $.
verina61-compute-suffix-graph-syntax
  $a wff ( VERINA61ComputeSuffixGraph A B ) $.
verina61-compute-suffix-syntax
  $a class ( VERINA61ComputeSuffix A ) $.
verina61-result-graph-syntax
  $a wff ( VERINA61ResultGraph A B ) $.
verina61-precondition-syntax
  $a wff ( VERINA61Pre A ) $.
verina61-program-syntax
  $a class ( VERINA61ProductExceptSelf A ) $.
verina61-nat-min-syntax
  $a class ( VERINA61NatMin A B ) $.
verina61-take-graph-syntax
  $a wff ( VERINA61TakeGraph A B C ) $.
verina61-take-syntax
  $a class ( VERINA61Take A B ) $.
verina61-drop-graph-syntax
  $a wff ( VERINA61DropGraph A B C ) $.
verina61-drop-syntax
  $a class ( VERINA61Drop A B ) $.
verina61-myprod-graph-syntax
  $a wff ( VERINA61MyProdGraph A B ) $.
verina61-myprod-syntax
  $a class ( VERINA61MyProd A ) $.
verina61-postcondition-syntax
  $a wff ( VERINA61Post A B ) $.

${
  $d k A B $.

  verina61-compute-pref-graph-definition $a |- (
    VERINA61ComputePrefGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      (
        ( # ` B ) = ( ( # ` A ) + 1 )
        /\
        ( B ` 0 ) = 1
      )
      /\
      A. k e. ( 0 ..^ ( # ` A ) )
        (
          B ` ( k + 1 )
        ) = (
          ( B ` k ) x. ( A ` k )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina61-compute-pref-definition $a |- (
    VERINA61ComputePref A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA61ComputePrefGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina61-reverse-graph-definition $a |- (
    VERINA61ReverseGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          B ` i
        ) = (
          A ` ( ( ( # ` A ) - 1 ) - i )
        )
    )
  ) $.
$}

${
  $d k r s A B $.

  verina61-compute-suffix-graph-definition $a |- (
    VERINA61ComputeSuffixGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    E. r e. Word ZZ
      E. s e. Word ZZ
        (
          (
            ( VERINA61ReverseGraph A r )
            /\
            (
              ( # ` s ) = ( ( # ` r ) + 1 )
              /\
              ( s ` 0 ) = 1
            )
          )
          /\
          (
            A. k e. ( 0 ..^ ( # ` r ) )
              (
                s ` ( k + 1 )
              ) = (
                ( s ` k ) x. ( r ` k )
              )
            /\
            ( VERINA61ReverseGraph s B )
          )
        )
  ) $.
$}

${
  $d y A $.

  verina61-compute-suffix-definition $a |- (
    VERINA61ComputeSuffix A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA61ComputeSuffixGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina61-result-graph-definition $a |- (
    VERINA61ResultGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          ( B ` i )
        ) = (
          ( ( VERINA61ComputePref A ) ` i )
          x.
          ( ( VERINA61ComputeSuffix A ) ` ( i + 1 ) )
        )
    )
  ) $.
$}

verina61-precondition-definition $a |- (
  VERINA61Pre A
) <-> (
  A e. Word ZZ
) $.

${
  $d y A $.

  verina61-program-definition $a |- (
    VERINA61ProductExceptSelf A
  ) = if (
    ( # ` A ) = 0 ,
    (/) ,
    iota_ y e. Word ZZ
      ( VERINA61ResultGraph A y )
  ) $.
$}

verina61-nat-min-definition $a |- (
  VERINA61NatMin A B
) = if (
  A < B ,
  A ,
  B
) $.

${
  $d j A B C $.

  verina61-take-graph-definition $a |- (
    VERINA61TakeGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      (
        # ` C
      ) = (
        VERINA61NatMin B ( # ` A )
      )
      /\
      A. j e. ( 0 ..^ ( # ` C ) )
        ( C ` j ) = ( A ` j )
    )
  ) $.
$}

${
  $d y A B $.

  verina61-take-definition $a |- (
    VERINA61Take A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA61TakeGraph A B y )
  ) $.
$}

${
  $d j A B C $.

  verina61-drop-graph-definition $a |- (
    VERINA61DropGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      (
        # ` C
      ) = (
        ( # ` A ) - ( VERINA61NatMin B ( # ` A ) )
      )
      /\
      A. j e. ( 0 ..^ ( # ` C ) )
        (
          C ` j
        ) = (
          A ` ( ( VERINA61NatMin B ( # ` A ) ) + j )
        )
    )
  ) $.
$}

${
  $d y A B $.

  verina61-drop-definition $a |- (
    VERINA61Drop A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA61DropGraph A B y )
  ) $.
$}

${
  $d k s A B $.

  verina61-myprod-graph-definition $a |- (
    VERINA61MyProdGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    E. s e. Word ZZ
      (
        (
          ( # ` s ) = ( ( # ` A ) + 1 )
          /\
          ( s ` ( # ` A ) ) = 1
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              s ` k
            ) = (
              ( A ` k ) x. ( s ` ( k + 1 ) )
            )
          /\
          B = ( s ` 0 )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina61-myprod-definition $a |- (
    VERINA61MyProd A
  ) = (
    iota_ y e. ZZ
      ( VERINA61MyProdGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina61-postcondition-definition $a |- (
    VERINA61Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          B ` i
        ) = (
          (
            VERINA61MyProd
              ( VERINA61Take A i )
          )
          x.
          (
            VERINA61MyProd
              ( VERINA61Drop A ( i + 1 ) )
          )
        )
    )
  ) $.
$}

verina-advanced-61-product-except-self $a |- A. w e. Word ZZ
  (
    ( VERINA61Pre w )
    ->
    (
      VERINA61Post
        w
        ( VERINA61ProductExceptSelf w )
    )
  )
$.
