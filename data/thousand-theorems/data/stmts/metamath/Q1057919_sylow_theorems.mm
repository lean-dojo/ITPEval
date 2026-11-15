$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1057919
  (thousand-theorems__metamath__Q1057919), "Sylow theorems": existence of
  subgroups of prime-power order, conjugacy of Sylow subgroups, and divisibility
  and modular-congruence properties of the number of Sylow subgroups. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's native class ( P pSyl G ) is the set of maximal P-subgroups of G,
  matching the Sylow subtype in the Lean source. Q1057919Conj is conjugation by
  g, written with the group subtraction operation as g * x * g^-1.

  Lean's Subgroup.index is Nat.card of the left-coset quotient, hence is zero
  when that quotient is infinite. SetMM's hash operation instead returns +oo
  on infinite sets, so Q1057919Index uses a conditional to preserve Lean's
  zero-on-infinite convention exactly.

  The four final $a assertions correspond, in source order, to
  Sylow.exists_subgroup_card_pow_prime, Sylow.isPretransitive_of_finite,
  Sylow.card_dvd_index, and card_sylow_modEq_one. Only the first assertion
  assumes that the group carrier is finite; the other three retain the source
  assumption that the set of Sylow subgroups is finite. These assertions are
  unproved and add no $p proof statements.
$)

$c Q1057919Conj Q1057919Index $.

q1057919-conj-syntax $a class ( Q1057919Conj G g H ) $.
q1057919-index-syntax $a class ( Q1057919Index G H ) $.

${
  $d G H g x $.

  q1057919-conj-definition $a |- ( Q1057919Conj G g H ) =
    ran (
      x e. H |->
      ( ( g ( +g ` G ) x ) ( -g ` G ) g )
    )
  $.
$}

${
  $d G H $.

  q1057919-index-definition $a |- ( Q1057919Index G H ) =
    if (
      ( ( Base ` G ) /. ( G ~QG H ) ) e. Fin
      ,
      ( # ` ( ( Base ` G ) /. ( G ~QG H ) ) )
      ,
      0
    )
  $.
$}

${
  $d G H N P $.

  thousand-theorems-q1057919-exists-subgroup $a |- (
    A. G A. P A. N
      (
        (
          G e. Grp
          /\
          ( Base ` G ) e. Fin
          /\
          P e. Prime
          /\
          N e. NN0
          /\
          ( P ^ N ) || ( # ` ( Base ` G ) )
        )
        ->
        E. H e. ( SubGrp ` G )
          ( # ` H ) = ( P ^ N )
      )
  ) $.
$}

${
  $d G H K P g $.

  thousand-theorems-q1057919-sylow-conjugacy $a |- (
    A. G A. P
      (
        (
          G e. Grp
          /\
          P e. Prime
          /\
          ( P pSyl G ) e. Fin
        )
        ->
        A. H e. ( P pSyl G )
          A. K e. ( P pSyl G )
            E. g e. ( Base ` G )
              ( Q1057919Conj G g H ) = K
      )
  ) $.
$}

${
  $d G H P $.

  thousand-theorems-q1057919-card-divides-index $a |- (
    A. G A. P A. H
      (
        (
          G e. Grp
          /\
          P e. Prime
          /\
          ( P pSyl G ) e. Fin
          /\
          H e. ( P pSyl G )
        )
        ->
        ( # ` ( P pSyl G ) ) || ( Q1057919Index G H )
      )
  ) $.
$}

${
  $d G P $.

  thousand-theorems-q1057919-card-modeq-one $a |- (
    A. G A. P
      (
        (
          G e. Grp
          /\
          P e. Prime
          /\
          ( P pSyl G ) e. Fin
        )
        ->
        (
          ( ( # ` ( P pSyl G ) ) mod P )
          =
          ( 1 mod P )
        )
      )
  ) $.
$}
