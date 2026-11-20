% A rule and a fact entail the conjecture.
fof(mortals, axiom, ![X]: (human(X) => mortal(X))).
fof(socrates_is_human, axiom, human(socrates)).
fof(socrates_is_mortal, conjecture, mortal(socrates)).
