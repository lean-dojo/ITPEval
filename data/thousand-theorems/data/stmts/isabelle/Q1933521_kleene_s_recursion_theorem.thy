(*
  Statement-only formalization of the thousand-theorems corpus artifact Q1933521,
  "Kleene's recursion theorem": every binary partial-recursive function of a
  program code and a natural input has a code whose unary partial evaluation
  equals the function specialized to that same code. This file contains no proof.
*)

theory Q1933521_kleene_s_recursion_theorem
  imports Main
begin

datatype q1933521_code =
    Q1933521_Zero
  | Q1933521_Succ
  | Q1933521_Left
  | Q1933521_Right
  | Q1933521_Pair q1933521_code q1933521_code
  | Q1933521_Comp q1933521_code q1933521_code
  | Q1933521_Prec q1933521_code q1933521_code
  | Q1933521_Rfind q1933521_code

definition q1933521_nat_pair :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "q1933521_nat_pair a b =
    (if a < b then b * b + a else a * a + a + b)"

fun q1933521_code_encode :: "q1933521_code \<Rightarrow> nat" where
  "q1933521_code_encode Q1933521_Zero = 0"
| "q1933521_code_encode Q1933521_Succ = 1"
| "q1933521_code_encode Q1933521_Left = 2"
| "q1933521_code_encode Q1933521_Right = 3"
| "q1933521_code_encode (Q1933521_Pair cf cg) =
    2 * (2 * q1933521_nat_pair
      (q1933521_code_encode cf) (q1933521_code_encode cg)) + 4"
| "q1933521_code_encode (Q1933521_Comp cf cg) =
    2 * (2 * q1933521_nat_pair
      (q1933521_code_encode cf) (q1933521_code_encode cg) + 1) + 4"
| "q1933521_code_encode (Q1933521_Prec cf cg) =
    2 * (2 * q1933521_nat_pair
      (q1933521_code_encode cf) (q1933521_code_encode cg)) + 5"
| "q1933521_code_encode (Q1933521_Rfind cf) =
    2 * (2 * q1933521_code_encode cf + 1) + 5"

inductive q1933521_code_eval ::
    "q1933521_code \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  eval_zero:
    "q1933521_code_eval Q1933521_Zero x 0"
| eval_succ:
    "q1933521_code_eval Q1933521_Succ x (Suc x)"
| eval_left:
    "q1933521_code_eval Q1933521_Left (q1933521_nat_pair a b) a"
| eval_right:
    "q1933521_code_eval Q1933521_Right (q1933521_nat_pair a b) b"
| eval_pair:
    "\<lbrakk>q1933521_code_eval cf x y; q1933521_code_eval cg x z\<rbrakk>
      \<Longrightarrow> q1933521_code_eval
        (Q1933521_Pair cf cg) x (q1933521_nat_pair y z)"
| eval_comp:
    "\<lbrakk>q1933521_code_eval cg x y; q1933521_code_eval cf y z\<rbrakk>
      \<Longrightarrow> q1933521_code_eval (Q1933521_Comp cf cg) x z"
| eval_prec_zero:
    "q1933521_code_eval cf a z
      \<Longrightarrow> q1933521_code_eval
        (Q1933521_Prec cf cg) (q1933521_nat_pair a 0) z"
| eval_prec_succ:
    "\<lbrakk>q1933521_code_eval
        (Q1933521_Prec cf cg) (q1933521_nat_pair a k) i;
      q1933521_code_eval cg
        (q1933521_nat_pair a (q1933521_nat_pair k i)) z\<rbrakk>
      \<Longrightarrow> q1933521_code_eval
        (Q1933521_Prec cf cg) (q1933521_nat_pair a (Suc k)) z"
| eval_rfind:
    "\<lbrakk>q1933521_code_eval cf (q1933521_nat_pair a (m + k)) 0;
      \<And>j. j < k \<Longrightarrow>
        \<exists>z. q1933521_code_eval cf
          (q1933521_nat_pair a (m + j)) z \<and> z \<noteq> 0\<rbrakk>
      \<Longrightarrow> q1933521_code_eval
        (Q1933521_Rfind cf) (q1933521_nat_pair a m) (m + k)"

type_synonym q1933521_partial_function = "nat \<Rightarrow> nat option"

definition q1933521_partrec2 ::
    "(q1933521_code \<Rightarrow> q1933521_partial_function) \<Rightarrow> bool" where
  "q1933521_partrec2 f \<longleftrightarrow>
    (\<exists>program. \<forall>c n y.
      q1933521_code_eval program
        (q1933521_nat_pair (q1933521_code_encode c) n) y
        \<longleftrightarrow> f c n = Some y)"

theorem kleene_second_recursion:
  fixes f :: "q1933521_code \<Rightarrow> q1933521_partial_function"
  assumes "q1933521_partrec2 f"
  shows "\<exists>c. \<forall>n y.
    q1933521_code_eval c n y \<longleftrightarrow> f c n = Some y"
  sorry

end
