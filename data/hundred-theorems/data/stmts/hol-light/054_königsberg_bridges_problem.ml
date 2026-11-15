(* ========================================================================= *)
(* Impossibility of Eulerian path for bridges of Koenigsberg.                *)
(* ========================================================================= *)

let edges = new_definition
  `edges(E:E->bool,V:V->bool,Ter:E->V->bool) = E`;;

let vertices = new_definition
  `vertices(E:E->bool,V:V->bool,Ter:E->V->bool) = V`;;

let termini = new_definition
  `termini(E:E->bool,V:V->bool,Ter:E->V->bool) = Ter`;;

(* ------------------------------------------------------------------------- *)
(* Definition of an undirected graph.                                        *)
(* ------------------------------------------------------------------------- *)

let graph = new_definition
 `graph G <=>
        !e. e IN edges(G)
            ==> ?a b. a IN vertices(G) /\ b IN vertices(G) /\
                      termini G e = {a,b}`;;

let TERMINI_IN_VERTICES = `!G e v. graph G /\ e IN edges(G) /\ v IN termini G e ==> v IN vertices G`;;

(* ------------------------------------------------------------------------- *)
(* Connection in a graph.                                                    *)
(* ------------------------------------------------------------------------- *)

let connects = new_definition
 `connects G e (a,b) <=> termini G e = {a,b}`;;

(* ------------------------------------------------------------------------- *)
(* Delete an edge in a graph.                                                *)
(* ------------------------------------------------------------------------- *)

let delete_edge = new_definition
 `delete_edge e (E,V,Ter) = (E DELETE e,V,Ter)`;;

let DELETE_EDGE_CLAUSES = `(!G. edges(delete_edge e G) = (edges G) DELETE e) /\
   (!G. vertices(delete_edge e G) = vertices G) /\
   (!G. termini(delete_edge e G) = termini G)`;;

let GRAPH_DELETE_EDGE = `!G e. graph G ==> graph(delete_edge e G)`;;

(* ------------------------------------------------------------------------- *)
(* Local finiteness: set of edges with given endpoint is finite.             *)
(* ------------------------------------------------------------------------- *)

let locally_finite = new_definition
 `locally_finite G <=>
     !v. v IN vertices(G) ==> FINITE {e | e IN edges G /\ v IN termini G e}`;;

(* ------------------------------------------------------------------------- *)
(* Degree of a vertex.                                                       *)
(* ------------------------------------------------------------------------- *)

let localdegree = new_definition
 `localdegree G v e =
        if termini G e = {v} then 2
        else if v IN termini G e then 1
        else 0`;;

let degree = new_definition
 `degree G v = nsum {e | e IN edges G /\ v IN termini G e} (localdegree G v)`;;

let DEGREE_DELETE_EDGE = `!G e:E v:V.
        graph G /\ locally_finite G /\ e IN edges(G)
        ==> degree G v =
                if termini G e = {v} then degree (delete_edge e G) v + 2
                else if v IN termini G e then degree (delete_edge e G) v + 1
                else degree (delete_edge e G) v`;;

(* ------------------------------------------------------------------------- *)
(* Definition of Eulerian path.                                              *)
(* ------------------------------------------------------------------------- *)

let eulerian_RULES,eulerian_INDUCT,eulerian_CASES = new_inductive_definition
 `(!G a. a IN vertices G /\ edges G = {} ==> eulerian G [] (a,a)) /\
  (!G a b c e es. e IN edges(G) /\ connects G e (a,b) /\
                  eulerian (delete_edge e G) es (b,c)
                  ==> eulerian G (CONS e es) (a,c))`;;

let EULERIAN_FINITE = `!G es ab. eulerian G es ab ==> FINITE (edges G)`;;

(* ------------------------------------------------------------------------- *)
(* The main result.                                                          *)
(* ------------------------------------------------------------------------- *)

let EULERIAN_ODD_LEMMA = `!G:(E->bool)#(V->bool)#(E->V->bool) es ab.
        eulerian G es ab
        ==> graph G
            ==> FINITE(edges G) /\
                !v. v IN vertices G
                    ==> (ODD(degree G v) <=>
                         ~(FST ab = SND ab) /\ (v = FST ab \/ v = SND ab))`;;

let EULERIAN_ODD = `!G es a b.
        graph G /\ eulerian G es (a,b)
        ==> !v. v IN vertices G
                ==> (ODD(degree G v) <=> ~(a = b) /\ (v = a \/ v = b))`;;

(* ------------------------------------------------------------------------- *)
(* Now the actual Koenigsberg configuration.                                 *)
(* ------------------------------------------------------------------------- *)

let KOENIGSBERG = `!G. vertices(G) = {0,1,2,3} /\
       edges(G) = {10,20,30,40,50,60,70} /\
       termini G (10) = {0,1} /\
       termini G (20) = {0,2} /\
       termini G (30) = {0,3} /\
       termini G (40) = {1,2} /\
       termini G (50) = {1,2} /\
       termini G (60) = {2,3} /\
       termini G (70) = {2,3}
       ==> ~(?es a b. eulerian G es (a,b))`;;

(******

Maybe for completeness I should show the contrary: existence of Eulerian
circuit/walk if we do have the right properties, assuming the graph is
connected; cf:

http://math.arizona.edu/~lagatta/class/fa05/m105/graphtheorynotes.pdf

 *****)
