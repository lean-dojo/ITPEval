$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/mergesort_list_OCamlMergesort_rev_sortqtvc
  (ntp4vc__metamath__pearl/mergesort_list_OCamlMergesort_rev_sortqtvc):
  the OCaml-style reverse mergesort verification condition establishes
  recursive split obligations and states that every returned list is sorted
  in reverse and permutes the requested input prefix. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt, R is its total preorder,
  and Word U is exactly the type of arbitrary finite zero-based U-lists. S is
  the source inductive sorted predicate, represented as the least subset of
  Word U closed under its empty, singleton, and ordered-cons constructors.
  The source sorted_mem and sorted_append laws are retained explicitly.

  P is prefix1 at the theorem's selected Inhabited elt instance. It remains
  an arbitrary total function from an integer and a U-list to a U-list,
  subject only to the source zero and positive-cons equations over the full
  unbounded integer domain ZZ.

  NTP4VCPerm compares every element's occurrence count, which is equivalent
  in both directions to List.Perm on finite words. NTP4VCReverse is exact word
  reversal. NTP4VCTDiv2 is signed integer division by two truncated toward
  zero; under the source hypothesis 2 <= n this is the Why3 quotient n / 2
  and agrees with the Lean Int.tdiv and Isabelle cdiv exports. The Rocq
  export's Z.rem at this position is a proposition-changing export defect.

  The remaining predicates only factor the original nested verification
  condition. Expanding their biconditional definitions recovers both base
  cases, every integer bound, prefix decomposition, recursive continuation,
  sorting and permutation premise, merge precondition, executable result
  branch, and final universally quantified postcondition. All list witnesses
  remain internally quantified. The final $a declaration is Metamath's native
  unproved statement encoding; every preceding $a is syntax or a faithful
  definition, and this database contains no $p declaration.
$)

$c
  NTP4VCPerm NTP4VCReverse NTP4VCTDiv2
  NTP4VCHas2 NTP4VCHas3 NTP4VCRev2 NTP4VCRev3
  NTP4VCRecursiveObligations NTP4VCRevSortObligations
  NTP4VCRevSortRun NTP4VCRevSortVC
$.

ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B C ) $.
ntp4vc-reverse-syntax
  $a class ( NTP4VCReverse A ) $.
ntp4vc-tdiv2-syntax
  $a class ( NTP4VCTDiv2 A ) $.
ntp4vc-has-two-syntax
  $a wff ( NTP4VCHas2 A B ) $.
ntp4vc-has-three-syntax
  $a wff ( NTP4VCHas3 A B ) $.
ntp4vc-reverse-two-syntax
  $a wff ( NTP4VCRev2 A B C D ) $.
ntp4vc-reverse-three-syntax
  $a wff ( NTP4VCRev3 A B C D ) $.
ntp4vc-recursive-obligations-syntax
  $a wff ( NTP4VCRecursiveObligations A B C D E F ) $.
ntp4vc-rev-sort-obligations-syntax
  $a wff ( NTP4VCRevSortObligations A B C D E F ) $.
ntp4vc-rev-sort-run-syntax
  $a wff ( NTP4VCRevSortRun A B C D E F G ) $.
ntp4vc-rev-sort-vc-syntax
  $a wff ( NTP4VCRevSortVC A B C D E F ) $.

${
  $d k v A B C $.

  ntp4vc-perm-definition $a |- (
    NTP4VCPerm A B C
  ) <->
  (
    (
      A e. Word C
      /\
      B e. Word C
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. v e. C
        (
          (
            # `
            { k e. ( 0 ..^ ( # ` A ) ) | ( A ` k ) = v }
          )
          =
          (
            # `
            { k e. ( 0 ..^ ( # ` B ) ) | ( B ` k ) = v }
          )
        )
    )
  ) $.
$}

${
  $d i A $.

  ntp4vc-reverse-definition $a |- (
    NTP4VCReverse A
  ) = (
    i e. ( 0 ..^ ( # ` A ) ) |->
      ( A ` ( ( ( # ` A ) - 1 ) - i ) )
  ) $.
$}

ntp4vc-tdiv2-definition $a |- (
  NTP4VCTDiv2 A
) = if (
  A < 0 ,
  ( |^ ` ( A / 2 ) ) ,
  ( |_ ` ( A / 2 ) )
) $.

${
  $d t x y A B $.

  ntp4vc-has-two-definition $a |- (
    NTP4VCHas2 A B
  ) <->
  (
    A e. Word B
    /\
    E. x e. B E. y e. B E. t e. Word B
      A = ( <" x "> ++ ( <" y "> ++ t ) )
  ) $.
$}

${
  $d t x y z A B $.

  ntp4vc-has-three-definition $a |- (
    NTP4VCHas3 A B
  ) <->
  (
    A e. Word B
    /\
    E. x e. B E. y e. B E. z e. B E. t e. Word B
      A = (
        <" x "> ++
        ( <" y "> ++ ( <" z "> ++ t ) )
      )
  ) $.
$}

${
  $d t x y A B C D $.

  ntp4vc-reverse-two-definition $a |- (
    NTP4VCRev2 A B C D
  ) <->
  E. x e. D E. y e. D E. t e. Word D
    (
      A = ( <" x "> ++ ( <" y "> ++ t ) )
      /\
      (
        (
          -. <. x , y >. e. C
          /\
          B = ( <" x "> ++ <" y "> )
        )
        \/
        (
          <. x , y >. e. C
          /\
          B = ( <" y "> ++ <" x "> )
        )
      )
    ) $.
$}

${
  $d t x y z A B C D $.

  ntp4vc-reverse-three-definition $a |- (
    NTP4VCRev3 A B C D
  ) <->
  E. x e. D E. y e. D E. z e. D E. t e. Word D
    (
      A = (
        <" x "> ++
        ( <" y "> ++ ( <" z "> ++ t ) )
      )
      /\
      (
        (
          (
            -. <. x , y >. e. C
            /\
            -. <. y , z >. e. C
          )
          /\
          B = (
            <" x "> ++
            ( <" y "> ++ <" z "> )
          )
        )
        \/
        (
          (
            (
              -. <. x , y >. e. C
              /\
              <. y , z >. e. C
            )
            /\
            -. <. x , z >. e. C
          )
          /\
          B = (
            <" x "> ++
            ( <" z "> ++ <" y "> )
          )
        )
        \/
        (
          (
            (
              -. <. x , y >. e. C
              /\
              <. y , z >. e. C
            )
            /\
            <. x , z >. e. C
          )
          /\
          B = (
            <" z "> ++
            ( <" x "> ++ <" y "> )
          )
        )
        \/
        (
          (
            <. x , y >. e. C
            /\
            -. <. x , z >. e. C
          )
          /\
          B = (
            <" y "> ++
            ( <" x "> ++ <" z "> )
          )
        )
        \/
        (
          (
            (
              <. x , y >. e. C
              /\
              <. x , z >. e. C
            )
            /\
            -. <. y , z >. e. C
          )
          /\
          B = (
            <" y "> ++
            ( <" z "> ++ <" x "> )
          )
        )
        \/
        (
          (
            (
              <. x , y >. e. C
              /\
              <. x , z >. e. C
            )
            /\
            <. y , z >. e. C
          )
          /\
          B = (
            <" z "> ++
            ( <" y "> ++ <" x "> )
          )
        )
      )
    ) $.
$}

${
  $d q s t x y A B C D E F $.

  ntp4vc-recursive-obligations-definition $a |- (
    NTP4VCRecursiveObligations A B C D E F
  ) <->
  (
    2 =/= 0
    /\
    (
      (
        0 <_ ( NTP4VCTDiv2 A )
        /\
        ( NTP4VCTDiv2 A ) <_ ( # ` B )
      )
      /\
      A. q e. Word F
        (
          B = (
            ( C ` <. ( NTP4VCTDiv2 A ) , B >. )
            ++
            q
          )
          ->
          (
            (
              (
                0 <_ A
                /\
                ( NTP4VCTDiv2 A ) < A
              )
              /\
              (
                2 <_ ( NTP4VCTDiv2 A )
                /\
                ( NTP4VCTDiv2 A ) <_ ( # ` B )
              )
            )
            /\
            A. s e. Word F
              (
                (
                  s e. E
                  /\
                  (
                    NTP4VCPerm
                      s
                      ( C ` <. ( NTP4VCTDiv2 A ) , B >. )
                      F
                  )
                )
                ->
                (
                  (
                    (
                      0 <_ A
                      /\
                      ( A - ( NTP4VCTDiv2 A ) ) < A
                    )
                    /\
                    (
                      2 <_ ( A - ( NTP4VCTDiv2 A ) )
                      /\
                      (
                        A - ( NTP4VCTDiv2 A )
                      ) <_ ( # ` q )
                    )
                  )
                  /\
                  A. t e. Word F
                    (
                      (
                        t e. E
                        /\
                        (
                          NTP4VCPerm
                            t
                            (
                              C `
                              <.
                                ( A - ( NTP4VCTDiv2 A ) ) ,
                                q
                              >.
                            )
                            F
                        )
                      )
                      ->
                      (
                        (
                          (
                            ( NTP4VCReverse (/) ) e. E
                            /\
                            s e. E
                          )
                          /\
                          t e. E
                        )
                        /\
                        (
                          A. x e. F A. y e. F
                            (
                              x e. ran (/)
                              ->
                              (
                                y e. ran s
                                ->
                                <. x , y >. e. D
                              )
                            )
                          /\
                          A. x e. F A. y e. F
                            (
                              x e. ran (/)
                              ->
                              (
                                y e. ran t
                                ->
                                <. x , y >. e. D
                              )
                            )
                        )
                      )
                    )
                )
              )
          )
        )
    )
  ) $.
$}

ntp4vc-rev-sort-obligations-definition $a |- (
  NTP4VCRevSortObligations A B C D E F
) <->
(
  (
    A = 2
    /\
    ( NTP4VCHas2 B F )
  )
  \/
  (
    A =/= 2
    /\
    (
      (
        A = 3
        /\
        ( NTP4VCHas3 B F )
      )
      \/
      (
        A =/= 3
        /\
        ( NTP4VCRecursiveObligations A B C D E F )
      )
    )
  )
) $.

${
  $d q s t A B C D E F G $.

  ntp4vc-rev-sort-run-definition $a |- (
    NTP4VCRevSortRun A B C D E F G
  ) <->
  (
    (
      A = 2
      /\
      ( NTP4VCRev2 B C E G )
    )
    \/
    (
      A =/= 2
      /\
      (
        (
          A = 3
          /\
          ( NTP4VCRev3 B C E G )
        )
        \/
        (
          A =/= 3
          /\
          E. q e. Word G
            (
              B = (
                ( D ` <. ( NTP4VCTDiv2 A ) , B >. )
                ++
                q
              )
              /\
              E. s e. Word G
                (
                  (
                    s e. F
                    /\
                    (
                      NTP4VCPerm
                        s
                        ( D ` <. ( NTP4VCTDiv2 A ) , B >. )
                        G
                    )
                  )
                  /\
                  E. t e. Word G
                    (
                      (
                        t e. F
                        /\
                        (
                          NTP4VCPerm
                            t
                            (
                              D `
                              <.
                                ( A - ( NTP4VCTDiv2 A ) ) ,
                                q
                              >.
                            )
                            G
                        )
                      )
                      /\
                      (
                        ( NTP4VCReverse C ) e. F
                        /\
                        (
                          NTP4VCPerm
                            C
                            ( ( (/) ++ s ) ++ t )
                            G
                        )
                      )
                    )
                )
            )
        )
      )
    )
  ) $.
$}

${
  $d r A B C D E F $.

  ntp4vc-rev-sort-vc-definition $a |- (
    NTP4VCRevSortVC A B C D E F
  ) <->
  (
    ( NTP4VCRevSortObligations A B C D E F )
    /\
    A. r e. Word F
      (
        ( NTP4VCRevSortRun A B r C D E F )
        ->
        (
          ( NTP4VCReverse r ) e. E
          /\
          (
            NTP4VCPerm
              r
              ( C ` <. A , B >. )
              F
          )
        )
      )
  ) $.
$}

${
  $d k l m q r s t w x y z L N P R S U $.

  $( Source arbitrary inhabited carrier elt and total preorder le. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-le-relation $e |- R C_ ( U X. U ) $.

  ntp4vc-le-reflexive $e |- A. x e. U
    <. x , x >. e. R $.

  ntp4vc-le-transitive $e |- A. x e. U A. y e. U A. z e. U
    (
      (
        <. x , y >. e. R
        /\
        <. y , z >. e. R
      )
      ->
      <. x , z >. e. R
    ) $.

  ntp4vc-le-total $e |- A. x e. U A. y e. U
    (
      <. x , y >. e. R
      \/
      <. y , x >. e. R
    ) $.

  $( Exact least fixed-point presentation of the source sorted predicate. $)
  ntp4vc-sorted-subset $e |- S C_ Word U $.

  ntp4vc-sorted-empty $e |- (/) e. S $.

  ntp4vc-sorted-singleton $e |- A. x e. U
    <" x "> e. S $.

  ntp4vc-sorted-ordered-cons $e |- A. x e. U A. y e. U
    A. t e. Word U
      (
        (
          <. x , y >. e. R
          /\
          ( <" y "> ++ t ) e. S
        )
        ->
        ( <" x "> ++ <" y "> ++ t ) e. S
      ) $.

  ntp4vc-sorted-structural-induction $e |- A. q e. ~P S
    (
      (
        (/) e. q
        /\
        (
          A. x e. U <" x "> e. q
          /\
          A. x e. U A. y e. U A. t e. Word U
            (
              (
                <. x , y >. e. R
                /\
                ( <" y "> ++ t ) e. q
              )
              ->
              ( <" x "> ++ <" y "> ++ t ) e. q
            )
        )
      )
      ->
      q = S
    ) $.

  $( The source sorted_mem and sorted_append characterization axioms. $)
  ntp4vc-sorted-mem $e |- A. w e. Word U A. x e. U
    (
      (
        (
          A. y e. U
            (
              y e. ran w
              ->
              <. x , y >. e. R
            )
          /\
          w e. S
        )
        <->
        ( <" x "> ++ w ) e. S
      )
    ) $.

  ntp4vc-sorted-append $e |- A. l e. Word U A. m e. Word U
    (
      (
        (
          l e. S
          /\
          (
            m e. S
            /\
            A. x e. U A. y e. U
              (
                (
                  x e. ran l
                  /\
                  y e. ran m
                )
                ->
                <. x , y >. e. R
              )
          )
        )
        <->
        ( l ++ m ) e. S
      )
    ) $.

  $( Source operation prefix1 and its complete displayed equations. $)
  ntp4vc-prefix-function
    $e |- P e. ( ( Word U ) ^m ( ZZ X. Word U ) ) $.

  ntp4vc-prefix-zero $e |- A. w e. Word U
    ( P ` <. 0 , w >. ) = (/) $.

  ntp4vc-prefix-positive-cons $e |- A. k e. ZZ A. x e. U
    A. t e. Word U
      (
        0 < k
        ->
        (
          P ` <. k , ( <" x "> ++ t ) >.
        )
        =
        (
          <" x "> ++ ( P ` <. ( k - 1 ) , t >. )
        )
      ) $.

  $( Source theorem parameters N=n and L=l, followed by fact0 and fact1. $)
  ntp4vc-n-integer $e |- N e. ZZ $.
  ntp4vc-l-word $e |- L e. Word U $.
  ntp4vc-fact0 $e |- 2 <_ N $.
  ntp4vc-fact1 $e |- N <_ ( # ` L ) $.

  ntp4vc-pearl-mergesort-list-ocamlmergesort-rev-sort-vc
    $a |- ( NTP4VCRevSortVC N L P R S U ) $.
$}
