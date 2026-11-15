$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/register_allocation_DWP_wrapqtvc: the double-weakest-precondition
  wrapping verification condition turns a sound weak code and its
  state-indexed binary postcondition compatibility into a sound Hoare code.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A is the arbitrary inhabited Why3 address carrier, encoded as a nonempty
  set. NTP4VCState A is exactly the source record of an address-to-integer
  memory, an integer-to-integer register file, and a finite integer stack.
  NTP4VCInstr A is the disjoint tagged union of the five source instruction
  constructors, and finite words over it are exactly source instruction lists.

  B and C are the source exec and exec_list functions. Their scoped equations
  below reproduce every instruction case and the complete list recursion, so
  they are definitionally the source operations rather than unconstrained
  transition symbols.

  A Bool-valued predicate on states is represented by a subset of the state
  carrier; similarly, binary postconditions and weak-code transformers are
  subsets of the corresponding products. This is the characteristic-set
  bijection for the exact two-element Boolean carrier. Ordered pairs encode
  the source hcode and wcode records. Expanding NTP4VCWCodeOk,
  NTP4VCPostAt, and NTP4VCHCodeOk yields exactly the two source assumptions
  and the source conclusion with unchanged universal scopes. Every auxiliary
  $a declaration is syntax or a faithful definition, and the final $a is
  Metamath's native unproved statement encoding; there is no $p declaration.
$)

$c
  NTP4VCState NTP4VCInstr
  NTP4VCIload NTP4VCIneg NTP4VCIadd NTP4VCIpush NTP4VCIpop
  NTP4VCUpdate NTP4VCPostAt
  NTP4VCWCode NTP4VCHCode NTP4VCWCodeOk NTP4VCHCodeOk
$.

ntp4vc-state-syntax $a class ( NTP4VCState A ) $.
ntp4vc-instr-syntax $a class ( NTP4VCInstr A ) $.
ntp4vc-iload-syntax $a class ( NTP4VCIload A B ) $.
ntp4vc-ineg-syntax $a class ( NTP4VCIneg A ) $.
ntp4vc-iadd-syntax $a class ( NTP4VCIadd A B ) $.
ntp4vc-ipush-syntax $a class ( NTP4VCIpush A ) $.
ntp4vc-ipop-syntax $a class ( NTP4VCIpop A ) $.
ntp4vc-update-syntax $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-post-at-syntax $a class ( NTP4VCPostAt A B C ) $.
ntp4vc-wcode-syntax $a class ( NTP4VCWCode A ) $.
ntp4vc-hcode-syntax $a class ( NTP4VCHCode A ) $.
ntp4vc-wcode-ok-syntax $a wff ( NTP4VCWCodeOk A B C ) $.
ntp4vc-hcode-ok-syntax $a wff ( NTP4VCHCodeOk A B C ) $.

ntp4vc-state-definition $a |- (
  NTP4VCState A
) = (
  ( ZZ ^m A )
  X.
  ( ( ZZ ^m ZZ ) X. Word ZZ )
) $.

ntp4vc-iload-definition $a |- (
  NTP4VCIload A B
) = <. 0 , <. A , B >. >. $.

ntp4vc-ineg-definition $a |- (
  NTP4VCIneg A
) = <. 1 , A >. $.

ntp4vc-iadd-definition $a |- (
  NTP4VCIadd A B
) = <. 2 , <. A , B >. >. $.

ntp4vc-ipush-definition $a |- (
  NTP4VCIpush A
) = <. 3 , A >. $.

ntp4vc-ipop-definition $a |- (
  NTP4VCIpop A
) = <. 4 , A >. $.

ntp4vc-instr-definition $a |- (
  NTP4VCInstr A
) = (
  ( { 0 } X. ( A X. ZZ ) )
  u.
  (
    ( { 1 } X. ZZ )
    u.
    (
      ( { 2 } X. ( ZZ X. ZZ ) )
      u.
      (
        ( { 3 } X. ZZ )
        u.
        ( { 4 } X. ZZ )
      )
    )
  )
) $.

${
  $d z A B C $.

  ntp4vc-update-definition $a |- (
    NTP4VCUpdate A B C
  ) = (
    z e. ZZ |->
      if ( z = B , C , ( A ` z ) )
  ) $.
$}

${
  $d y A B C $.

  ntp4vc-post-at-definition $a |- (
    NTP4VCPostAt A B C
  ) = {
    y e. ( NTP4VCState A ) |
      <. C , y >. e. B
  } $.
$}

ntp4vc-wcode-definition $a |- (
  NTP4VCWCode A
) = (
  (
    ~P (
      ( ~P ( NTP4VCState A ) )
      X.
      ( NTP4VCState A )
    )
  )
  X.
  Word ( NTP4VCInstr A )
) $.

ntp4vc-hcode-definition $a |- (
  NTP4VCHCode A
) = (
  Word ( NTP4VCInstr A )
  X.
  ~P (
    ( NTP4VCState A )
    X.
    ( NTP4VCState A )
  )
) $.

${
  $d q s A B C $.

  ntp4vc-wcode-ok-definition $a |- (
    NTP4VCWCodeOk A B C
  ) <-> (
    A. q e. ~P ( NTP4VCState A )
      A. s e. ( NTP4VCState A )
        (
          <. q , s >. e. ( 1st ` C )
          ->
          (
            B ` <. ( 2nd ` C ) , s >.
          ) e. q
        )
  ) $.
$}

${
  $d s A B C $.

  ntp4vc-hcode-ok-definition $a |- (
    NTP4VCHCodeOk A B C
  ) <-> (
    A. s e. ( NTP4VCState A )
      <.
        s ,
        ( B ` <. ( 1st ` C ) , s >. )
      >. e. ( 2nd ` C )
  ) $.
$}

${
  $d i l m p q r s t v x A B C D E $.

  $( The arbitrary Why3 address type is a set and is inhabited. $)
  ntp4vc-address-carrier-set $e |- A e. _V $.
  ntp4vc-address-carrier-nonempty $e |- A =/= (/) $.

  $( Exact instruction execution function. $)
  ntp4vc-exec-instr-type $e |- B e. (
    ( NTP4VCState A )
    ^m
    (
      ( NTP4VCInstr A )
      X.
      ( NTP4VCState A )
    )
  ) $.

  ntp4vc-exec-load $e |- A. m e. ( ZZ ^m A )
    A. p e. ( ZZ ^m ZZ )
      A. t e. Word ZZ
        A. x e. A
          A. r e. ZZ
            (
              B ` <.
                ( NTP4VCIload x r ) ,
                <. m , <. p , t >. >.
              >.
            )
            =
            <.
              m ,
              <.
                ( NTP4VCUpdate p r ( m ` x ) ) ,
                t
              >.
            >. $.

  ntp4vc-exec-neg $e |- A. m e. ( ZZ ^m A )
    A. p e. ( ZZ ^m ZZ )
      A. t e. Word ZZ
        A. r e. ZZ
          (
            B ` <.
              ( NTP4VCIneg r ) ,
              <. m , <. p , t >. >.
            >.
          )
          =
          <.
            m ,
            <.
              ( NTP4VCUpdate p r ( -u ( p ` r ) ) ) ,
              t
            >.
          >. $.

  ntp4vc-exec-add $e |- A. m e. ( ZZ ^m A )
    A. p e. ( ZZ ^m ZZ )
      A. t e. Word ZZ
        A. q e. ZZ
          A. r e. ZZ
            (
              B ` <.
                ( NTP4VCIadd q r ) ,
                <. m , <. p , t >. >.
              >.
            )
            =
            <.
              m ,
              <.
                (
                  NTP4VCUpdate
                    p r
                    ( ( p ` q ) + ( p ` r ) )
                ) ,
                t
              >.
            >. $.

  ntp4vc-exec-push $e |- A. m e. ( ZZ ^m A )
    A. p e. ( ZZ ^m ZZ )
      A. t e. Word ZZ
        A. r e. ZZ
          (
            B ` <.
              ( NTP4VCIpush r ) ,
              <. m , <. p , t >. >.
            >.
          )
          =
          <.
            m ,
            <. p , ( <" ( p ` r ) "> ++ t ) >.
          >. $.

  ntp4vc-exec-pop-empty $e |- A. m e. ( ZZ ^m A )
    A. p e. ( ZZ ^m ZZ )
      A. r e. ZZ
        (
          B ` <.
            ( NTP4VCIpop r ) ,
            <. m , <. p , (/) >. >.
          >.
        )
        =
        <. m , <. p , (/) >. >. $.

  ntp4vc-exec-pop-cons $e |- A. m e. ( ZZ ^m A )
    A. p e. ( ZZ ^m ZZ )
      A. t e. Word ZZ
        A. v e. ZZ
          A. r e. ZZ
            (
              B ` <.
                ( NTP4VCIpop r ) ,
                <. m , <. p , ( <" v "> ++ t ) >. >.
              >.
            )
            =
            <.
              m ,
              <. ( NTP4VCUpdate p r v ) , t >.
            >. $.

  $( Exact recursive execution of a finite instruction list. $)
  ntp4vc-exec-list-type $e |- C e. (
    ( NTP4VCState A )
    ^m
    (
      Word ( NTP4VCInstr A )
      X.
      ( NTP4VCState A )
    )
  ) $.

  ntp4vc-exec-list-nil $e |- A. s e. ( NTP4VCState A )
    ( C ` <. (/) , s >. ) = s $.

  ntp4vc-exec-list-cons $e |- A. i e. ( NTP4VCInstr A )
    A. l e. Word ( NTP4VCInstr A )
      A. s e. ( NTP4VCState A )
        (
          C ` <. ( <" i "> ++ l ) , s >.
        )
        =
        (
          C ` <. l , ( B ` <. i , s >. ) >.
        ) $.

  $( Source theorem parameters wc and pst. $)
  ntp4vc-wcode-parameter $e |- D e. ( NTP4VCWCode A ) $.
  ntp4vc-post-parameter $e |- E C_ (
    ( NTP4VCState A )
    X.
    ( NTP4VCState A )
  ) $.

  $( fact0: wcode_ok wc. $)
  ntp4vc-fact0 $e |- ( NTP4VCWCodeOk A C D ) $.

  $( fact1: forall x. wc.trans (pst x) x. $)
  ntp4vc-fact1 $e |- A. x e. ( NTP4VCState A )
    <.
      ( NTP4VCPostAt A E x ) ,
      x
    >. e. ( 1st ` D ) $.

  ntp4vc-pearl-register-allocation-dwp-wrap-vc $a |- (
    NTP4VCHCodeOk
      A
      C
      <. ( 2nd ` D ) , E >.
  ) $.
$}
