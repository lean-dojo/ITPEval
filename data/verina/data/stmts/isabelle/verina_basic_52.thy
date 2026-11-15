(*
  Statement-only formalization of VERINA corpus artifact verina_basic_52
  (verina__isabelle__verina_basic_52), catalog title "BubbleSort": an
  executable bubble-sort program repeatedly swaps adjacent out-of-order
  integers and returns a pairwise nondecreasing permutation of the input,
  together with its unconditional precondition, postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_52
  imports Main
begin

definition BubbleSort_precond :: "int list \<Rightarrow> bool" where
  "BubbleSort_precond a \<longleftrightarrow> True"

definition bubbleSort_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "bubbleSort_getBang a i =
    (if i < length a then a ! i else 0)"

definition bubbleSort_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "bubbleSort_setBang a i x =
    (if i < length a then list_update a i x else a)"

definition bubbleSort_swap ::
    "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list" where
  "bubbleSort_swap a i j =
    (let temp = bubbleSort_getBang a i;
         a1 = bubbleSort_setBang a i (bubbleSort_getBang a j)
     in bubbleSort_setBang a1 j temp)"

fun bubbleInner_steps ::
    "nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list" where
  "bubbleInner_steps 0 j a = a"
| "bubbleInner_steps (Suc n) j a =
    (let a' =
       (if bubbleSort_getBang a j > bubbleSort_getBang a (j + 1)
        then bubbleSort_swap a j (j + 1)
        else a)
     in bubbleInner_steps n (j + 1) a')"

definition bubbleInner ::
    "nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list" where
  "bubbleInner j i a = bubbleInner_steps (i - j) j a"

fun bubbleOuter :: "nat \<Rightarrow> int list \<Rightarrow> int list" where
  "bubbleOuter 0 a = a"
| "bubbleOuter (Suc i) a =
    bubbleOuter i (bubbleInner 0 (Suc i) a)"

definition BubbleSort :: "int list \<Rightarrow> int list" where
  "BubbleSort a =
    (if length a = 0 then a else bubbleOuter (length a - 1) a)"

fun BubbleSort_pairwise_le :: "int list \<Rightarrow> bool" where
  "BubbleSort_pairwise_le [] = True"
| "BubbleSort_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     BubbleSort_pairwise_le xs)"

definition BubbleSort_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "BubbleSort_postcond a result \<longleftrightarrow>
    BubbleSort_pairwise_le result \<and>
    (\<forall>z. count_list result z = count_list a z)"

theorem BubbleSort_spec_satisfied:
  assumes "BubbleSort_precond a"
  shows "BubbleSort_postcond a (BubbleSort a)"
  sorry

end
