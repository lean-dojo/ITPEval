$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_40 (verina__metamath__verina_advanced_40), catalog title
  maxOfList: the exact recursive natural-number list program returns an
  element of every nonempty input list that bounds all its elements above.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA40HelperGraph gives the exact computation of the source local helper.
  Its trace begins at zero, the result for the empty list, and visits the
  input from right to left. At each step it returns the current element when
  that element is greater than the recursively computed tail result, and
  otherwise retains the tail result. For a singleton, comparison with the
  initial zero returns its sole natural-number element, exactly matching the
  source singleton branch. VERINA40Helper selects the unique trace result,
  and VERINA40MaxOfList is the source executable implementation.

  VERINA40Pre is the nonempty-list precondition. VERINA40Post says that the
  result occurs at an input position and that every input position contains
  a value at most the result, exactly representing List membership and the
  source boundedness clause. The proof-valued precondition argument is
  computationally and propositionally unused and is omitted from the target
  function and predicate. The final $a declaration is the source correctness
  proposition. Every earlier $a is syntax or a faithful definition, and this
  database has no $p declaration.
$)

$c
  VERINA40HelperGraph VERINA40Helper
  VERINA40Pre VERINA40MaxOfList VERINA40Post
$.

verina40-helper-graph-syntax
  $a wff ( VERINA40HelperGraph A B ) $.
verina40-helper-syntax
  $a class ( VERINA40Helper A ) $.
verina40-precondition-syntax
  $a wff ( VERINA40Pre A ) $.
verina40-max-of-list-syntax
  $a class ( VERINA40MaxOfList A ) $.
verina40-postcondition-syntax
  $a wff ( VERINA40Post A B ) $.

${
  $d k s A B $.

  verina40-helper-graph-definition $a |- (
    VERINA40HelperGraph A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    E. s e. Word NN0
      (
        (
          ( # ` s ) = ( ( # ` A ) + 1 )
          /\
          ( s ` 0 ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              s ` ( k + 1 )
            ) = (
              if (
                (
                  s ` k
                ) < (
                  A ` ( ( ( # ` A ) - 1 ) - k )
                )
                ,
                (
                  A ` ( ( ( # ` A ) - 1 ) - k )
                )
                ,
                ( s ` k )
              )
            )
          /\
          B = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina40-helper-definition $a |- (
    VERINA40Helper A
  ) = (
    iota_ y e. NN0
      ( VERINA40HelperGraph A y )
  ) $.
$}

verina40-precondition-definition $a |- (
  VERINA40Pre A
) <-> (
  A e. Word NN0
  /\
  0 < ( # ` A )
) $.

verina40-max-of-list-definition $a |- (
  VERINA40MaxOfList A
) = (
  VERINA40Helper A
) $.

${
  $d i j A B $.

  verina40-postcondition-definition $a |- (
    VERINA40Post A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    (
      E. i e. ( 0 ..^ ( # ` A ) )
        ( A ` i ) = B
      /\
      A. j e. ( 0 ..^ ( # ` A ) )
        ( A ` j ) <_ B
    )
  ) $.
$}

verina-advanced-40-max-of-list $a |- A. w e. Word NN0
  (
    ( VERINA40Pre w )
    ->
    (
      VERINA40Post
        w
        ( VERINA40MaxOfList w )
    )
  )
$.
