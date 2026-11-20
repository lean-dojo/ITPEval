(* The heap supplies the parent theories. Only theories introduced by this
   invocation are inspected. Native propositions retain locale premises. *)
local
  val output = TextIO.openOut (getenv "ITPEVAL_OUTPUT")
  fun hex c = StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX (Char.ord c))
  fun row fields = TextIO.output (output, space_implode "\t" (map (String.translate hex) fields) ^ "\n")
  fun plain s = XML.content_of (YXML.parse_body s)
  fun term_xml tm = YXML.string_of_body (Term_XML.Encode.term_raw tm)
  fun type_xml T = YXML.string_of_body (Term_XML.Encode.typ T)
  fun line p = Int.toString (the_default 0 (Position.line_of p))
  fun inspect thy =
    let
      val ctx = Proof_Context.init_global thy
      val name = Context.theory_long_name thy
      val parents = Theory.parents_of thy
      val path = Path.append (Resources.master_directory thy)
        (Path.basic (Context.theory_base_name thy ^ ".thy")) |> File.platform_path
      val _ = row ("theory" :: name :: path :: map Context.theory_long_name parents)
      val const_space = Sign.const_space thy
      fun const (c, (T, _)) =
        if exists (fn t => Name_Space.declared (Sign.const_space t) c) parents then ()
        else row ["decl", name, c, "constant", plain (Syntax.string_of_typ ctx T),
          line (ITPEval_Theory.position const_space c), "declared", "", "", type_xml T, "", ""]
      fun fact (named as (c, _)) =
        let
          val th = Global_Theory.get_thm_name thy (named, Position.none)
          val pos = ITPEval_Theory.position (Global_Theory.fact_space thy) c
          val status = if Thm_Deps.has_skip_proof [th] then "admitted"
            else if null (Thm_Deps.all_oracles [th]) then "kernel_checked" else "uses_oracle"
          val prop = Thm.prop_of th
          val hyps = map (plain o Syntax.string_of_term ctx) (Logic.strip_imp_prems prop @ Thm.hyps_of th)
          val deps = map (Thm_Name.print o #2) (Thm_Deps.thm_deps thy [th])
        in row ["decl", name, Thm_Name.print named, "fact", plain (Syntax.string_of_term ctx prop),
                line pos, status, space_implode "\000" hyps, space_implode "\000" deps, term_xml prop,
                space_implode "\000" (map term_xml (Thm.hyps_of th)),
                space_implode "\000" (Term.add_const_names prop [])] end
    in
      List.app const (#constants (Consts.dest (Sign.consts_of thy)));
      List.app fact (ITPEval_Theory.fact_names thy)
    end
in
  val _ = List.app inspect ITPEval_Theory.theories
  val _ = row ["done"]
  val _ = TextIO.closeOut output
end
