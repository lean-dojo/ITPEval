(*
  Statement-only formalization of the thousand-theorems corpus artifact Q1766814,
  "Smn theorem": a computable specialization function transforms a code and a
  fixed first input into a code with the same partial evaluation. This file
  contains no proof.
*)

theory Q1766814_smn_theorem
  imports Main
begin

datatype code =
    CZero
  | CSucc
  | CLeft
  | CRight
  | CPair code code
  | CComp code code
  | CPrec code code
  | CRfind code

definition nat_pair :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nat_pair a b =
    (if a < b then b * b + a else a * a + a + b)"

fun code_encode :: "code \<Rightarrow> nat" where
  "code_encode CZero = 0"
| "code_encode CSucc = 1"
| "code_encode CLeft = 2"
| "code_encode CRight = 3"
| "code_encode (CPair cf cg) =
    2 * (2 * nat_pair (code_encode cf) (code_encode cg)) + 4"
| "code_encode (CComp cf cg) =
    2 * (2 * nat_pair (code_encode cf) (code_encode cg) + 1) + 4"
| "code_encode (CPrec cf cg) =
    2 * (2 * nat_pair (code_encode cf) (code_encode cg)) + 5"
| "code_encode (CRfind cf) = 2 * (2 * code_encode cf + 1) + 5"

inductive code_eval :: "code \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  eval_zero:
    "code_eval CZero x 0"
| eval_succ:
    "code_eval CSucc x (Suc x)"
| eval_left:
    "code_eval CLeft (nat_pair a b) a"
| eval_right:
    "code_eval CRight (nat_pair a b) b"
| eval_pair:
    "\<lbrakk>code_eval cf x y; code_eval cg x z\<rbrakk>
      \<Longrightarrow> code_eval (CPair cf cg) x (nat_pair y z)"
| eval_comp:
    "\<lbrakk>code_eval cg x y; code_eval cf y z\<rbrakk>
      \<Longrightarrow> code_eval (CComp cf cg) x z"
| eval_prec_zero:
    "code_eval cf a z
      \<Longrightarrow> code_eval (CPrec cf cg) (nat_pair a 0) z"
| eval_prec_succ:
    "\<lbrakk>code_eval (CPrec cf cg) (nat_pair a k) i;
      code_eval cg (nat_pair a (nat_pair k i)) z\<rbrakk>
      \<Longrightarrow> code_eval (CPrec cf cg) (nat_pair a (Suc k)) z"
| eval_rfind:
    "\<lbrakk>code_eval cf (nat_pair a (m + k)) 0;
      \<And>j. j < k \<Longrightarrow>
        \<exists>z. code_eval cf (nat_pair a (m + j)) z \<and> z \<noteq> 0\<rbrakk>
      \<Longrightarrow> code_eval (CRfind cf) (nat_pair a m) (m + k)"

definition computable2 :: "(code \<Rightarrow> nat \<Rightarrow> code) \<Rightarrow> bool" where
  "computable2 f \<longleftrightarrow>
    (\<exists>p. \<forall>c n y.
      code_eval p (nat_pair (code_encode c) n) y
        \<longleftrightarrow> y = code_encode (f c n))"

theorem smn:
  "\<exists>f :: code \<Rightarrow> nat \<Rightarrow> code.
    computable2 f \<and>
    (\<forall>c n x y.
      code_eval (f c n) x y
        \<longleftrightarrow> code_eval c (nat_pair n x) y)"
  sorry

end
