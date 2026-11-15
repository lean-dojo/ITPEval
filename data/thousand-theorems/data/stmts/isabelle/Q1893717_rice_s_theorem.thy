(*
  Statement-only formalization of the thousand-theorems corpus artifact Q1893717,
  "Rice's theorem": every computably decidable extensional property of unary
  partial-recursive functions that contains one such function contains them all.
  This file contains no proof.
*)

theory Q1893717_rice_s_theorem
  imports Main
begin

type_synonym q1893717_registers = "nat \<Rightarrow> nat"
type_synonym q1893717_state = "nat \<times> q1893717_registers"
type_synonym q1893717_partial_function = "nat \<Rightarrow> nat option"

fun q1893717_encode_program :: "nat list \<Rightarrow> nat" where
  "q1893717_encode_program [] = 0"
| "q1893717_encode_program (instruction # program) =
    2 ^ instruction * (2 * q1893717_encode_program program + 1)"

definition q1893717_decode_program :: "nat \<Rightarrow> nat list" where
  "q1893717_decode_program code =
    (if \<exists>program. q1893717_encode_program program = code
     then THE program. q1893717_encode_program program = code
     else [])"

definition q1893717_unpair :: "nat \<Rightarrow> nat \<times> nat" where
  "q1893717_unpair code =
    (SOME pair. code =
      (fst pair + snd pair) * (fst pair + snd pair + 1) div 2 + snd pair)"

definition q1893717_instruction_tag :: "nat \<Rightarrow> nat" where
  "q1893717_instruction_tag instruction =
    fst (q1893717_unpair instruction) mod 3"

definition q1893717_instruction_arguments :: "nat \<Rightarrow> nat" where
  "q1893717_instruction_arguments instruction =
    snd (q1893717_unpair instruction)"

definition q1893717_instruction_register :: "nat \<Rightarrow> nat" where
  "q1893717_instruction_register instruction =
    fst (q1893717_unpair (q1893717_instruction_arguments instruction))"

definition q1893717_instruction_rest :: "nat \<Rightarrow> nat" where
  "q1893717_instruction_rest instruction =
    snd (q1893717_unpair (q1893717_instruction_arguments instruction))"

definition q1893717_instruction_target :: "nat \<Rightarrow> nat" where
  "q1893717_instruction_target instruction =
    fst (q1893717_unpair (q1893717_instruction_rest instruction))"

definition q1893717_instruction_other_target :: "nat \<Rightarrow> nat" where
  "q1893717_instruction_other_target instruction =
    snd (q1893717_unpair (q1893717_instruction_rest instruction))"

definition q1893717_halted ::
    "nat list \<Rightarrow> q1893717_state \<Rightarrow> bool" where
  "q1893717_halted program state \<longleftrightarrow>
    (case state of (pc, registers) \<Rightarrow>
      pc \<ge> length program \<or>
      q1893717_instruction_tag (program ! pc) = 0)"

definition q1893717_step ::
    "nat list \<Rightarrow> q1893717_state \<Rightarrow> q1893717_state" where
  "q1893717_step program state =
    (case state of (pc, registers) \<Rightarrow>
      if pc \<ge> length program then state
      else
        let instruction = program ! pc;
            tag = q1893717_instruction_tag instruction;
            r = q1893717_instruction_register instruction
        in if tag = 0 then state
           else if tag = 1 then
             (q1893717_instruction_target instruction,
              registers(r := Suc (registers r)))
           else if registers r = 0 then
             (q1893717_instruction_target instruction, registers)
           else
             (q1893717_instruction_other_target instruction,
              registers(r := registers r - 1)))"

definition q1893717_initial_state :: "nat \<Rightarrow> q1893717_state" where
  "q1893717_initial_state input =
    (0, (\<lambda>r. if r = 0 then input else 0))"

definition q1893717_reaches_halt ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "q1893717_reaches_halt program input output \<longleftrightarrow>
    (\<exists>steps.
      let state =
        (q1893717_step program ^^ steps) (q1893717_initial_state input)
      in q1893717_halted program state \<and> snd state 0 = output)"

definition q1893717_eval :: "nat \<Rightarrow> q1893717_partial_function" where
  "q1893717_eval code input =
    (let program = q1893717_decode_program code
     in if \<exists>output. q1893717_reaches_halt program input output
        then Some (THE output. q1893717_reaches_halt program input output)
        else None)"

definition q1893717_partrec :: "q1893717_partial_function \<Rightarrow> bool" where
  "q1893717_partrec f \<longleftrightarrow> (\<exists>code. q1893717_eval code = f)"

definition q1893717_computable_pred :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "q1893717_computable_pred predicate \<longleftrightarrow>
    (\<exists>code. \<forall>input.
      q1893717_eval code input =
        Some (if predicate input then 1 else 0))"

theorem rice:
  fixes C :: "q1893717_partial_function set"
    and f g :: q1893717_partial_function
  assumes decidable_property:
      "q1893717_computable_pred (\<lambda>code. q1893717_eval code \<in> C)"
    and f_partial_recursive: "q1893717_partrec f"
    and g_partial_recursive: "q1893717_partrec g"
    and f_has_property: "f \<in> C"
  shows "g \<in> C"
  sorry

end
