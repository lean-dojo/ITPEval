$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_29
  (verina__metamath__verina_basic_29), catalog title removeElement: the exact
  executable valid-index array deletion removes the selected integer entry,
  preserves the preceding prefix, shifts the following suffix left by one,
  and satisfies the complete length-and-index correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup,
  0 ..^ ( # ` w ) is its complete valid-index set, and ++ is exact word
  concatenation.

  VERINAB29GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB29NatSub is
  Lean's truncated natural subtraction, and VERINAB29NatMin is natural
  minimum.

  VERINAB29TakeGraph and VERINAB29DropGraph reproduce the finite-word
  semantics of taking and dropping a natural number of array entries.
  VERINAB29Take and VERINAB29Drop select their unique results.
  VERINAB29RemoveElement concatenates the first k entries with the entries
  after index k, exactly the valid-index branch of Array.eraseIdx!. The source
  precondition makes the panic branch unreachable, so this definition fixes
  the same executable result independently of the postcondition and admits no
  additional outputs.

  VERINAB29Pre is exactly k < s.size. VERINAB29Post preserves the source
  result-size equation and both nested universal implications over natural
  indices, including get!-lookup behavior. The proof-valued precondition
  arguments to the implementation and postcondition have no computational or
  propositional effect beyond the explicit antecedent in the final correctness
  assertion. Every earlier $a is syntax or a faithful definition required by
  this rendering, and this database has no $p declaration.
$)

$c
  VERINAB29GetBang VERINAB29NatSub VERINAB29NatMin
  VERINAB29TakeGraph VERINAB29Take
  VERINAB29DropGraph VERINAB29Drop
  VERINAB29Pre VERINAB29RemoveElement VERINAB29Post
$.

verinab29-get-bang-syntax
  $a class ( VERINAB29GetBang A B ) $.
verinab29-nat-sub-syntax
  $a class ( VERINAB29NatSub A B ) $.
verinab29-nat-min-syntax
  $a class ( VERINAB29NatMin A B ) $.
verinab29-take-graph-syntax
  $a wff ( VERINAB29TakeGraph A B C ) $.
verinab29-take-syntax
  $a class ( VERINAB29Take A B ) $.
verinab29-drop-graph-syntax
  $a wff ( VERINAB29DropGraph A B C ) $.
verinab29-drop-syntax
  $a class ( VERINAB29Drop A B ) $.
verinab29-precondition-syntax
  $a wff ( VERINAB29Pre A B ) $.
verinab29-program-syntax
  $a class ( VERINAB29RemoveElement A B ) $.
verinab29-postcondition-syntax
  $a wff ( VERINAB29Post A B C ) $.

verinab29-get-bang-definition $a |- (
  VERINAB29GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab29-nat-sub-definition $a |- (
  VERINAB29NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab29-nat-min-definition $a |- (
  VERINAB29NatMin A B
) = if (
  A < B ,
  A ,
  B
) $.

${
  $d i A B C $.

  verinab29-take-graph-definition $a |- (
    VERINAB29TakeGraph A B C
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
      ( # ` C ) = (
        VERINAB29NatMin B ( # ` A )
      )
      /\
      A. i e. ( 0 ..^ ( # ` C ) )
        ( C ` i ) = ( A ` i )
    )
  ) $.
$}

${
  $d y A B $.

  verinab29-take-definition $a |- (
    VERINAB29Take A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB29TakeGraph A B y )
  ) $.
$}

${
  $d i A B C $.

  verinab29-drop-graph-definition $a |- (
    VERINAB29DropGraph A B C
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
      ( # ` C ) = (
        ( # ` A ) - (
          VERINAB29NatMin B ( # ` A )
        )
      )
      /\
      A. i e. ( 0 ..^ ( # ` C ) )
        (
          C ` i
        ) = (
          A ` (
            ( VERINAB29NatMin B ( # ` A ) ) + i
          )
        )
    )
  ) $.
$}

${
  $d y A B $.

  verinab29-drop-definition $a |- (
    VERINAB29Drop A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB29DropGraph A B y )
  ) $.
$}

verinab29-precondition-definition $a |- (
  VERINAB29Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. NN0
  )
  /\
  B < ( # ` A )
) $.

verinab29-program-definition $a |- (
  VERINAB29RemoveElement A B
) = (
  ( VERINAB29Take A B )
  ++
  ( VERINAB29Drop A ( B + 1 ) )
) $.

${
  $d i A B C $.

  verinab29-postcondition-definition $a |- (
    VERINAB29Post A B C
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
      ( # ` C ) = (
        VERINAB29NatSub ( # ` A ) 1
      )
      /\
      (
        A. i e. NN0
          (
            i < B
            ->
            (
              VERINAB29GetBang C i
            ) = (
              VERINAB29GetBang A i
            )
          )
        /\
        A. i e. NN0
          (
            i < ( # ` C )
            ->
            (
              B <_ i
              ->
              (
                VERINAB29GetBang C i
              ) = (
                VERINAB29GetBang A ( i + 1 )
              )
            )
          )
      )
    )
  ) $.
$}

verina-basic-29-remove-element $a |- A. s e. Word ZZ
  A. k e. NN0
    (
      ( VERINAB29Pre s k )
      ->
      (
        VERINAB29Post
          s
          k
          ( VERINAB29RemoveElement s k )
      )
    )
$.
