$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_21
  (verina__metamath__verina_basic_21), catalog title isSublist: the exact
  executable left-to-right Boolean search decides whether one arbitrary
  finite integer list occurs contiguously in another, together with its
  unconditional correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set. The Boolean domain is
  represented by { 0 , 1 }, with false = 0 and true = 1.

  VERINAB21Window A B i says that A equals
  (B.drop i).take A.length. The explicit bound i + A.length <= B.length
  fixes the taken word's length to A.length, and the pointwise clause fixes
  every entry to B[i + k], so this is exactly the source list equality in
  every branch where it is evaluated.

  VERINAB21CheckGraph is the least relation closed under the four exact
  branches of the source local recursion check. An index whose window extends
  beyond B returns false. A matching in-range window returns true. A
  nonmatching in-range window recurses at i + 1 when that index is at most
  B.length, and otherwise returns false. VERINAB21Check selects the unique
  Boolean output of this terminating graph. VERINAB21IsSublist first preserves
  the source A.length > B.length false branch and otherwise invokes check at
  zero. Thus the executable result is fixed independently of the
  postcondition and admits no additional outputs.

  VERINAB21Pre is the source True precondition on typed List Int inputs.
  VERINAB21Post preserves the existential natural index, bounded contiguous
  window equality, and equivalence with the Boolean result. The proof-valued
  precondition argument is computationally and propositionally unused and is
  represented by the explicit antecedent in the final correctness assertion.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINAB21Window
  VERINAB21CheckGraph VERINAB21Check
  VERINAB21Pre VERINAB21IsSublist VERINAB21Post
$.

verinab21-window-syntax
  $a wff ( VERINAB21Window A B C ) $.
verinab21-check-graph-syntax
  $a wff ( VERINAB21CheckGraph A B C D ) $.
verinab21-check-syntax
  $a class ( VERINAB21Check A B C ) $.
verinab21-precondition-syntax
  $a wff ( VERINAB21Pre A B ) $.
verinab21-program-syntax
  $a class ( VERINAB21IsSublist A B ) $.
verinab21-postcondition-syntax
  $a wff ( VERINAB21Post A B C ) $.

${
  $d k A B C $.

  verinab21-window-definition $a |- (
    VERINAB21Window A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. NN0
    )
    /\
    (
      ( C + ( # ` A ) ) <_ ( # ` B )
      /\
      A. k e. ( 0 ..^ ( # ` A ) )
        ( A ` k ) = ( B ` ( C + k ) )
    )
  ) $.
$}

${
  $d R A B C D i y $.

  verinab21-check-graph-definition $a |- (
    VERINAB21CheckGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. Word ZZ
        )
        /\
        C e. NN0
      )
      /\
      D e. { 0 , 1 }
    )
    /\
    A. R
      (
        (
          (
            A. i e. NN0
              (
                ( # ` B ) < ( i + ( # ` A ) )
                ->
                <.
                  <. <. A , B >. , i >.
                  ,
                  0
                >. e. R
              )
            /\
            A. i e. NN0
              (
                ( VERINAB21Window A B i )
                ->
                <.
                  <. <. A , B >. , i >.
                  ,
                  1
                >. e. R
              )
          )
          /\
          (
            A. i e. NN0
              A. y e. { 0 , 1 }
                (
                  (
                    (
                      (
                        ( i + ( # ` A ) ) <_ ( # ` B )
                        /\
                        -. ( VERINAB21Window A B i )
                      )
                      /\
                      ( i + 1 ) <_ ( # ` B )
                    )
                    /\
                    <.
                      <. <. A , B >. , ( i + 1 ) >.
                      ,
                      y
                    >. e. R
                  )
                  ->
                  <.
                    <. <. A , B >. , i >.
                    ,
                    y
                  >. e. R
                )
            /\
            A. i e. NN0
              (
                (
                  (
                    (
                      ( i + ( # ` A ) ) <_ ( # ` B )
                      /\
                      -. ( VERINAB21Window A B i )
                    )
                    /\
                    ( # ` B ) < ( i + 1 )
                  )
                )
                ->
                <.
                  <. <. A , B >. , i >.
                  ,
                  0
                >. e. R
              )
          )
        )
        ->
        <.
          <. <. A , B >. , C >.
          ,
          D
        >. e. R
      )
  ) $.
$}

${
  $d y A B C $.

  verinab21-check-definition $a |- (
    VERINAB21Check A B C
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINAB21CheckGraph A B C y )
  ) $.
$}

verinab21-precondition-definition $a |- (
  VERINAB21Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. Word ZZ
) $.

verinab21-program-definition $a |- (
  VERINAB21IsSublist A B
) = if (
  ( # ` B ) < ( # ` A ) ,
  0 ,
  ( VERINAB21Check A B 0 )
) $.

${
  $d i A B C $.

  verinab21-postcondition-definition $a |- (
    VERINAB21Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. { 0 , 1 }
    )
    /\
    (
      E. i e. NN0
        ( VERINAB21Window A B i )
      <->
      C = 1
    )
  ) $.
$}

verina-basic-21-is-sublist $a |-
  A. s e. Word ZZ
    A. m e. Word ZZ
      (
        ( VERINAB21Pre s m )
        ->
        (
          VERINAB21Post
            s
            m
            ( VERINAB21IsSublist s m )
        )
      )
$.
