theory comp_commute
  imports Main
begin

definition myComp :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)"
  where "myComp g f \<equiv> \<lambda>x. g (f x)"

definition myId :: "'a \<Rightarrow> 'a"
  where "myId \<equiv> \<lambda>x. x"



lemma comp_assoc:
  "myComp h (myComp g f) = myComp (myComp h g) f"
  sorry
lemma comp_id_l:
  "myComp myId f = f"
  sorry
lemma comp_id_r:
  "myComp f myId = f"
  sorry


definition commute :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "commute f g \<equiv> myComp f g = myComp g f"

lemma commute_symm:
  "commute f g \<Longrightarrow> commute g f"
  sorry
lemma commute_with_id_l:
  "commute f myId"
  sorry
lemma commute_with_id_r:
  "commute myId f"
  sorry
lemma commute_refl:
  "commute f f"
  sorry
lemma commute_congr:
  "f1 = f2 \<Longrightarrow> g1 = g2 \<Longrightarrow> commute f1 g1 \<Longrightarrow> commute f2 g2"
  sorry
lemma commute_transport_left_id:
  "commute f g \<Longrightarrow> commute (myComp myId f) g"
  sorry
lemma commute_transport_right_id:
  "commute f g \<Longrightarrow> commute f (myComp myId g)"
  sorry
end
