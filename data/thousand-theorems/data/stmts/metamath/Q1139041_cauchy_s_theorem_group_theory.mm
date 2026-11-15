$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1139041
  (thousand-theorems__metamath__Q1139041), "Cauchy's theorem (group theory)":
  every prime dividing the order of a finite group is the order of some group
  element. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, G e. Grp supplies an arbitrary group, Base ` G is its carrier,
  Fin and # express finiteness and finite cardinality, Prime is the class of
  natural primes, || is divisibility, and ( od ` G ) ` x is the order of the
  carrier element x.

  The element witness remains existentially quantified inside the conclusion,
  exactly as in exists_prime_orderOf_dvd_card. The final declaration is the
  single unproved $a corpus statement; the root artifact source contains no
  $p proof statement.
$)

${
  $d G P x $.

  thousand-theorems-q1139041-cauchy $a |- (
    A. G A. P
      (
        (
          G e. Grp
          /\
          ( Base ` G ) e. Fin
          /\
          P e. Prime
          /\
          P || ( # ` ( Base ` G ) )
        )
        ->
        E. x e. ( Base ` G )
          ( ( od ` G ) ` x ) = P
      )
  ) $.
$}
