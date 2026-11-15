$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_42 (verina__metamath__verina_advanced_42), catalog title
  maxProfit: an exact executable scan of an arbitrary finite natural-number
  price list computes the greatest profit from buying before selling, with
  the zero-profit and attaining-transaction correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  SetMM subtraction is ordinary integer subtraction, so VERINA42NatSub
  explicitly restores Lean's truncated Nat.sub on natural arguments. When
  A < B it returns zero; otherwise B <= A and the ordinary integer A - B is
  nonnegative and equals Nat.sub. Every source subtraction is represented by
  this definition: the current transaction profit, the tail length (including
  the empty-list case), and both postcondition transaction profits. Thus each
  subtraction remains equivalent for all natural inputs, not only when the
  minuend happens to exceed the subtrahend.

  VERINA42State is the pair (minimum price so far, maximum profit so far).
  VERINA42Update is exactly updateMinAndProfit: it replaces the minimum by
  the lesser of the old minimum and current price, computes current price
  minus the old minimum only when the price is larger, and retains the
  larger of that profit and the old maximum.

  VERINA42AuxGraph records the unique complete left-to-right trace of those
  updates for arbitrary helper arguments. VERINA42MaxProfitAux selects the
  final profit component, exactly implementing maxProfitAux.
  VERINA42TailGraph and VERINA42Tail give List.tail. VERINA42MaxProfit is the
  source match: zero on the empty list, and otherwise the helper on the tail
  initialized with the head price and zero profit.

  VERINA42Pre is the source True precondition together with the List Nat
  input type. VERINA42Post expands zipIdx over the complete index range. Its
  first clause is List.Pairwise on all earlier/later entries, its second
  clause characterizes zero result by absence of a profitable ordered
  transaction (including the explicit length-at-most-one disjunct), and its
  third clause requires a positive result to be attained by an ordered
  transaction. The proof-valued precondition argument is computationally
  and propositionally unused and is omitted from the target function and
  predicate. The final $a declaration is the source correctness
  proposition. Every earlier $a is syntax or a faithful definition, and
  this database has no $p declaration.
$)

$c
  VERINA42NatSub VERINA42State VERINA42Update
  VERINA42AuxGraph VERINA42MaxProfitAux
  VERINA42TailGraph VERINA42Tail
  VERINA42Pre VERINA42MaxProfit VERINA42Post
$.

verina42-nat-sub-syntax
  $a class ( VERINA42NatSub A B ) $.
verina42-state-syntax
  $a class VERINA42State $.
verina42-update-syntax
  $a class ( VERINA42Update A B C ) $.
verina42-aux-graph-syntax
  $a wff ( VERINA42AuxGraph A B C D ) $.
verina42-max-profit-aux-syntax
  $a class ( VERINA42MaxProfitAux A B C ) $.
verina42-tail-graph-syntax
  $a wff ( VERINA42TailGraph A B ) $.
verina42-tail-syntax
  $a class ( VERINA42Tail A ) $.
verina42-precondition-syntax
  $a wff ( VERINA42Pre A ) $.
verina42-max-profit-syntax
  $a class ( VERINA42MaxProfit A ) $.
verina42-postcondition-syntax
  $a wff ( VERINA42Post A B ) $.

verina42-nat-sub-definition $a |- (
  VERINA42NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verina42-state-definition $a |- VERINA42State = (
  NN0 X. NN0
) $.

verina42-update-definition $a |- (
  VERINA42Update A B C
) = <.
  if (
    A < B ,
    A ,
    B
  )
  ,
  if (
    C < if (
      B < A ,
      ( VERINA42NatSub A B ) ,
      0
    )
    ,
    if (
      B < A ,
      ( VERINA42NatSub A B ) ,
      0
    )
    ,
    C
  )
>. $.

${
  $d k t A B C D $.

  verina42-aux-graph-definition $a |- (
    VERINA42AuxGraph A B C D
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      (
        C e. NN0
        /\
        D e. NN0
      )
    )
    /\
    E. t e. Word VERINA42State
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = <. B , C >.
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              t ` ( k + 1 )
            ) = (
              VERINA42Update
                ( A ` k )
                ( 1st ` ( t ` k ) )
                ( 2nd ` ( t ` k ) )
            )
          /\
          D = ( 2nd ` ( t ` ( # ` A ) ) )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verina42-max-profit-aux-definition $a |- (
    VERINA42MaxProfitAux A B C
  ) = (
    iota_ y e. NN0
      ( VERINA42AuxGraph A B C y )
  ) $.
$}

${
  $d j A B $.

  verina42-tail-graph-definition $a |- (
    VERINA42TailGraph A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. Word NN0
    )
    /\
    (
      ( # ` B ) = ( VERINA42NatSub ( # ` A ) 1 )
      /\
      A. j e. ( 0 ..^ ( # ` B ) )
        ( B ` j ) = ( A ` ( j + 1 ) )
    )
  ) $.
$}

${
  $d y A $.

  verina42-tail-definition $a |- (
    VERINA42Tail A
  ) = (
    iota_ y e. Word NN0
      ( VERINA42TailGraph A y )
  ) $.
$}

verina42-precondition-definition $a |- (
  VERINA42Pre A
) <-> (
  A e. Word NN0
) $.

verina42-max-profit-definition $a |- (
  VERINA42MaxProfit A
) = if (
  ( # ` A ) = 0 ,
  0 ,
  (
    VERINA42MaxProfitAux
      ( VERINA42Tail A )
      ( A ` 0 )
      0
  )
) $.

${
  $d i j A B $.

  verina42-postcondition-definition $a |- (
    VERINA42Post A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    (
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i < j
            ->
            (
              VERINA42NatSub ( A ` j ) ( A ` i )
            ) <_ B
          )
      /\
      (
        (
          B = 0
          <->
          (
            ( # ` A ) <_ 1
            \/
            A. i e. ( 0 ..^ ( # ` A ) )
              A. j e. ( 0 ..^ ( # ` A ) )
                (
                  j <_ i
                  \/
                  ( A ` j ) <_ ( A ` i )
                )
          )
        )
        /\
        (
          0 < B
          ->
          E. i e. ( 0 ..^ ( # ` A ) )
            E. j e. ( 0 ..^ ( # ` A ) )
              (
                i < j
                /\
                (
                  VERINA42NatSub ( A ` j ) ( A ` i )
                ) = B
              )
        )
      )
    )
  ) $.
$}

verina-advanced-42-max-profit $a |- A. w e. Word NN0
  (
    ( VERINA42Pre w )
    ->
    (
      VERINA42Post
        w
        ( VERINA42MaxProfit w )
    )
  )
$.
