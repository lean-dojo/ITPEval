(* Read the theorem database after Holmake has exported the local theories. *)
val root = OS.FileSys.getDir ();
val target = valOf (OS.Process.getEnv "ITPEVAL_THEORY");
val output = TextIO.openOut (valOf (OS.Process.getEnv "ITPEVAL_OUTPUT"));
val _ = loadPath := (OS.Path.concat (root, ".hol/objs")) :: root :: !loadPath;
val _ = load (target ^ "Theory");
fun hex c = StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX (Char.ord c));
fun row fields =
  TextIO.output (output, String.concatWith "\t" (map (String.translate hex) fields) ^ "\n");
fun inspect name =
  let
    val parents = Theory.parents name
    val _ = row ("theory" :: name :: parents)
    (* The paths encode ordered children. Each node comes from the kernel term
       constructors, including the theory namespace of an instantiated constant. *)
    fun tree id label path tm =
      let
        val emit = fn fields => row (["term", name, id, label, path,
                                      Parse.type_to_string (Term.type_of tm)] @ fields)
        fun children kind (left, right) =
          (emit [kind]; tree id label (path ^ "0") left; tree id label (path ^ "1") right)
      in
        if Term.is_var tm then emit ["variable", #1 (Term.dest_var tm)]
        else if Term.is_const tm then
          let val {Thy,Name,...} = Term.dest_thy_const tm in emit ["constant",Thy,Name] end
        else if Term.is_comb tm then children "application" (Term.dest_comb tm)
        else children "abstraction" (Term.dest_abs tm)
      end
    fun entry ((_, id), (th, {class, loc, private})) =
      let
        val kind = case class of DB.Axm => "axiom" | DB.Def => "definition" | DB.Thm => "theorem"
        val (line,exact) = case loc of
            DB.Located {linenum,exact,...} => (Int.toString linenum,Bool.toString exact)
          | DB.Unknown => ("0","false")
        val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
        val _ = tree id "conclusion" "" (Thm.concl th)
        val _ = List.foldl (fn (tm,i) => (tree id ("hypothesis-" ^ Int.toString i) "" tm; i+1)) 0 (Thm.hyp th)
      in row (["decl", name, id, kind, Parse.term_to_string (Thm.concl th), line, exact,
               String.concatWith "\000" oracles, String.concatWith "\000" axioms,
               Bool.toString private] @ map Parse.term_to_string (Thm.hyp th)) end
  in List.app entry (DB.thy name) end;
val _ = List.app inspect (List.filter
  (fn name => OS.FileSys.access (name ^ "Script.sml", [OS.FileSys.A_READ]))
  (target :: Theory.ancestry target));
val _ = row ["done"];
val _ = TextIO.closeOut output;
