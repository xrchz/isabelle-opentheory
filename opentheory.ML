(* opentheory.ML *)
(* version: Isabelle2019 *)


signature OPENTHEORY =
sig
  val read_article : string -> (string * string) list -> theory -> theory
  val get_thms : theory -> thm list
  val add_thm : attribute
  val del_thm : attribute
  val add_tyop : string * string -> theory -> theory
  val add_const : string * string -> theory -> theory
  val setup : theory -> theory
end


structure OpenTheory : OPENTHEORY = struct

exception ERR of string

val freeze_thm = Thm.unvarify_global

fun internal_err msg = raise ERR ("Internal error: " ^ msg)

(** Theory data **)

structure OT_Thms = Generic_Data
(
  type T = thm Termtab.table
  val empty = Termtab.empty
  val extend = I
  val merge = Termtab.merge (K true)
)

structure OT_Consts = Theory_Data
(
  type T = string Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (op =)
)

structure OT_TyOps = Theory_Data
(
  type T = string Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (op =)
)

val get_thms =
  map snd o Termtab.dest o OT_Thms.get o Context.Theory

local
  fun key_of th = Logic.list_implies (Thm.hyps_of th, Thm.concl_of th) 
  val fix_typ = Term.map_atyps (fn T => case T of TVar ((name, _), sort) => TFree (name, sort) | _ => T)
  val fix_term = Term.map_types fix_typ
  fun fix_thm thm =
    let val get_ctyp = Thm.global_ctyp_of (Thm.theory_of_thm thm)
    in Thm.instantiate (Term.add_tvars (Thm.prop_of thm) [] 
                          |> map (fn x => (x, get_ctyp (fix_typ (TVar x)))), []) thm
    end
in


val add_thm =
  Thm.declaration_attribute (fn th => OT_Thms.map (Termtab.update (key_of th |> fix_term, fix_thm th)))
val del_thm =
  Thm.declaration_attribute (fn th => OT_Thms.map (Termtab.delete (key_of th |> fix_term)))


end

fun add_const data = OT_Consts.map (Symtab.update data)

fun add_tyop data = OT_TyOps.map (Symtab.update data)

val setup =
  Attrib.setup
    (Binding.name "opentheory")
    (Attrib.add_del add_thm del_thm)
    "declaration of opentheory theorem"
  #>
  Global_Theory.add_thms_dynamic
    (Binding.name "opentheory", map snd o Termtab.dest o OT_Thms.get)


(** Operations on types, terms, and theorems **)

type tyop = string
type const = string
type var = cterm
type trm = cterm

fun print_cterm t =
  Syntax.string_of_term_global (Thm.theory_of_cterm t) (Thm.term_of t)

(* Constructing types *)

(* preparing type variables *)
val typeS = @{sort "type"}
fun prime a = "'" ^ a

(* bool <-> prop *)
fun mk_prop t = Thm.apply @{cterm Trueprop} t
fun un_prop t = Thm.dest_arg t

(* = <-> == *)
fun mk_meta th = 
  let
    val xy = un_prop (Thm.cprop_of th)
    val x = Thm.dest_arg1 xy
    val y = Thm.dest_arg xy
    val a = Thm.ctyp_of_cterm x
    val T = Thm.typ_of a

    val rule = Thm.instantiate ([((("'a", 0), typeS), a)], 
                                [((("x", 0), T), x), ((("y", 0), T), y)]) eq_reflection

    val th' = Thm.implies_elim rule th
    val (x', y') = Logic.dest_equals (Thm.concl_of th')
    val _ = if (Thm.term_of x) aconv x' then () else internal_err "mk_meta"
    val _ = if (Thm.term_of y) aconv y' then () else internal_err "mk_meta"
  in
    th'
  end


fun un_meta th =
  let
    val xy = Thm.cprop_of th
    val x = Thm.dest_arg1 xy
    val y = Thm.dest_arg xy
    val a = Thm.ctyp_of_cterm x
    val T = Thm.typ_of a

    val rule = Thm.instantiate ([((("'a", 0), typeS), a)], 
                                [((("A", 0), T), x), ((("B", 0), T), y)]) meta_eq_to_obj_eq

    val th' = Thm.implies_elim rule th
    val (x', y') = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.concl_of th'))
    val _ = if (Thm.term_of x) aconv x' then () else internal_err "un_meta"
    val _ = if (Thm.term_of y) aconv y' then () else internal_err "un_meta"
  in
    th'
  end

fun assume t = Thm.assume (mk_prop t)

fun abs_thm v th =
  let
    val n = fst (dest_Free (Thm.term_of v))
  in
    un_meta (Thm.abstract_rule n v (mk_meta th))
  end

fun app_thm th1 th2 =
  let
    val th3 = un_meta (Thm.combination (mk_meta th1) (mk_meta th2))

    (* Correctness check *)
    val (f, g) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.concl_of th1))
    val (x, y) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.concl_of th2))
    val eq1 = HOLogic.dest_Trueprop (Thm.concl_of th3)
    val eq2 = HOLogic.mk_eq (f $ x, g $ y)
    val _ = if eq1 aconv eq2 then () 
     else internal_err ("app_thm: " ^ Syntax.string_of_term_global (Thm.theory_of_thm th1) eq1
                         ^ " " ^ Syntax.string_of_term_global (Thm.theory_of_thm th2) eq2  )
  in
    th3
  end



fun beta_conv t = un_meta (Thm.beta_conversion false t)
fun refl t = un_meta (Thm.reflexive t)



(* lookup in translation tables *)
fun find_thm tab ts t thy =
  let
    (* FIXME: should sort ts first? *)
    val prems = map mk_prop ts
    val concl = mk_prop t
    val prop = Drule.list_implies (prems, concl)
    val ths = Termtab.lookup tab (Thm.term_of prop)
  in
    case ths of
      NONE => (case ((try (Goal.prove_global thy [] (map Thm.term_of prems) (Thm.term_of concl))) 
                      (fn {prems, context} => (FIRSTGOAL (Method.insert_tac context prems)
                                                     THEN (safe_asm_full_simp_tac context 1)))) of
                SOME th => let val s = Syntax.string_of_term_global thy (Thm.prop_of th)
                               val _ = writeln ("axiom[opentheory] : \"" ^ s ^ "\" proved.")
                               in (freeze_thm thy th, thy) end (* in (Thm.legacy_freezeT th, thy) end *)
              | NONE => 
                         raise ERR ("missing axiom: " ^
                          ML_Syntax.print_list print_cterm ts ^ " |- " ^ print_cterm t))

    | SOME th => (th, thy)
  end


fun iff_elim th1 (*Q=P*) th2 (*Q*) : thm (*P*) =
  let
    val QP = Thm.dest_arg (Thm.cprop_of th1)
    val Q = Thm.dest_arg1 QP
    val P = Thm.dest_arg QP
    val Q' = Thm.dest_arg (Thm.cprop_of th2)
    val _ = if (Thm.term_of Q) aconv (Thm.term_of Q')
            then () else let val thy = Thm.theory_of_thm th1
                         in
                           internal_err ("iff_elim: " ^ Syntax.string_of_term_global thy (Thm.prop_of th1)
                                          ^ "\n" ^ Syntax.string_of_term_global thy (Thm.term_of QP)
                                          ^ "\n" ^ Syntax.string_of_term_global thy (Thm.term_of Q)
                                          ^ "\n" ^ Syntax.string_of_term_global thy (Thm.term_of Q'))
                         end

    val rule = Thm.instantiate ([], [((("Q", 0), HOLogic.boolT), Q), 
                                     ((("P", 0), HOLogic.boolT), P)]) iffD1

    val th3 = Thm.implies_elim (Thm.implies_elim rule th1) th2 

    (* Correctness check *)
    val PQ = HOLogic.dest_Trueprop (Thm.concl_of th1)
    val P = HOLogic.dest_Trueprop (Thm.concl_of th2)
    val Q = HOLogic.dest_Trueprop (Thm.concl_of th3)
    val PQ' = HOLogic.mk_eq (P, Q)
    val _ = if PQ aconv PQ' then () else internal_err "iff_elim 2"

  in
    th3
  end


fun define_const
    (s : string)
    (rhs : trm)
    (thy : theory)
     T
  : (const * thm) * theory =
(case T of
  NONE =>
  let
    val bind = Binding.qualified_name s (* FIXME: do proper name translation *)
    val typ = Thm.typ_of (Thm.ctyp_of_cterm rhs)
    val _ = writeln (s ^ " :: " ^ Syntax.string_of_typ_global thy typ)
    val (lhs, thy) = Sign.declare_const_global ((bind, typ), NoSyn) thy
    val eqn = Logic.mk_equals (lhs, Thm.term_of rhs)
    val def = Thm.no_attributes (Binding.suffix_name "_def" bind, eqn)
    val (def_thm, thy) = yield_singleton (Global_Theory.add_defs false) def thy

    val def_thm = freeze_thm thy def_thm
    (* TODO: Correctness check *)
    (* def_thm might be incorrect if rhs is not beta-normal *)
    val const = fst (dest_Const lhs)
    (* register constant name in database *)
    val thy = add_const (s, const) thy
  in
    ((const, un_meta def_thm), thy)
  end
| SOME tab => let val _ = Symtab.lookup tab s 
              in internal_err "overwriting of defined constants"
              end)
 

fun define_tyop
    (tyname : string)
    (abs : string)
    (rep : string)
    (args : string list)
    (ax : thm)
    (thy : theory)
  : (tyop * const * const * thm * thm) * theory =
  let
    val _ = writeln ("defining type: " ^ tyname)
    val ty_bind = Binding.qualified_name tyname
    val abs_bind = Binding.qualified_name abs
    val rep_bind = Binding.qualified_name rep
    val morphs = SOME (rep_bind, abs_bind)
    val args' = map prime args
    val typ = (ty_bind, map (fn a => (a, typeS)) args', NoSyn)
    val (phi, x) = Term.dest_comb (HOLogic.dest_Trueprop (Thm.concl_of ax))

    val oldT = fastype_of x 

    val set = HOLogic.Collect_const oldT $ phi
(* *)
    val mph = Typedef.make_morphisms ty_bind morphs
    val tac = (fn x => EVERY' [resolve_tac x [exI], resolve_tac x [CollectI], resolve_tac x [ax]] 1)
    val ((tyop, ({Rep_name, Abs_name, ...}, info)), thy) =
        Typedef.add_typedef_global {overloaded=false} typ set (SOME mph) tac thy
    val {type_definition, Rep_inverse, ...} = info

    (* instantiate Rep_inverse rule *)
    val certT = Thm.global_ctyp_of thy
    val cert = Thm.global_cterm_of thy
    val tfrees = map (fn a => TFree (a, typeS)) args'
    val tvars = map (fn a => ((a, 0), typeS)) args'
    val newT = Type (tyop, tfrees)
    val instT = map2 (fn x => fn y => (x, certT y)) tvars tfrees
    val inst = [((("x", 0), newT), cert (Free ("a", newT)))]
    val abs_rep = Thm.instantiate (instT, inst) Rep_inverse

    (* rebuild non-normalized type_definition rule *)
    val type_definition = Thm.instantiate (instT, []) type_definition
    val RepT = newT --> oldT
    val AbsT = oldT --> newT
    val phiT = oldT --> HOLogic.boolT
    val setT = Type ("Set.set", [oldT])
    val RepC = Const (Rep_name, RepT)
    val AbsC = Const (Abs_name, AbsT)
    val typedefT = RepT --> AbsT --> setT --> HOLogic.boolT
    val typedefC = Const (@{const_name type_definition}, typedefT)
    val cprop = cert (HOLogic.mk_Trueprop (typedefC $ RepC $ AbsC $ set))
    val eq_th = Thm.symmetric (Thm.beta_conversion true cprop)
    val type_definition = Thm.equal_elim eq_th type_definition

    (* instantiate Abs_inverse rule *)
    val instT = [((("'a", 0), typeS), certT newT),
                 ((("'b", 0), typeS), certT oldT)]
    val inst = [((("Rep", 0), RepT), cert RepC),
                ((("Abs", 0), AbsT), cert AbsC),
                ((("P", 0), phiT), cert phi),
                ((("r", 0), oldT), cert (Free ("r", oldT)))]

    val rule = Thm.instantiate (instT, inst) @{thm type_definition_Collect_iff}
    val rep_abs = Thm.implies_elim rule type_definition
  in
    ((tyop, Abs_name, Rep_name, abs_rep, rep_abs), thy)
  end



fun define_tyop6
    (tyname : string)
    (abs : string)
    (rep : string)
    (args : string list)
    (ax : thm)
    (thy : theory)
  : (tyop * const * const * thm * thm) * theory =
  let
    val _ = writeln ("defining type: " ^ tyname)
    val ty_bind = Binding.qualified_name tyname
    val abs_bind = Binding.qualified_name abs
    val rep_bind = Binding.qualified_name rep
    val morphs = SOME (rep_bind, abs_bind)
    val args' = map prime args
    val typ = (ty_bind, map (fn a => (a, typeS)) args', NoSyn)
    val (phi, x) = Term.dest_comb (HOLogic.dest_Trueprop (Thm.concl_of ax))
    val oldT = fastype_of x 

    val set = HOLogic.Collect_const oldT $ phi
(* *)
    val mph = Typedef.make_morphisms ty_bind morphs
    val tac = (fn x => EVERY' [resolve_tac x [exI], resolve_tac x [CollectI], resolve_tac x [ax]] 1)
    val ((tyop, ({Rep_name, Abs_name, ...}, info)), thy) =
        Typedef.add_typedef_global {overloaded=false} typ set (SOME mph) tac thy

    val {type_definition, Rep_inverse, ...} = info

    (* instantiate Rep_inverse rule *)
    val certT = Thm.global_ctyp_of thy
    val cert = Thm.global_cterm_of thy
    val tfrees = map (fn a => TFree (a, typeS)) args'
    val tvars = map (fn a => ((a, 0), typeS)) args'
    val newT = Type (tyop, tfrees)
    val instT = map2 (fn x => fn y => (x, certT y)) tvars tfrees
    val inst = [((("x", 0), newT), cert (Free ("a", newT)))]
    val abs_rep = un_meta(Thm.abstract_rule "a" (cert (Free ("a", newT))) 
                           (mk_meta(Thm.instantiate (instT, inst) Rep_inverse)))

    (* rebuild non-normalized type_definition rule *)
    val type_definition = Thm.instantiate (instT, []) type_definition
    val RepT = newT --> oldT
    val AbsT = oldT --> newT
    val phiT = oldT --> HOLogic.boolT
    val setT = Type ("Set.set", [oldT])
    val RepC = Const (Rep_name, RepT)
    val AbsC = Const (Abs_name, AbsT)
    val typedefT = RepT --> AbsT --> setT --> HOLogic.boolT
    val typedefC = Const (@{const_name type_definition}, typedefT)
    val cprop = cert (HOLogic.mk_Trueprop (typedefC $ RepC $ AbsC $ set))
    val eq_th = Thm.symmetric (Thm.beta_conversion true cprop)
    val type_definition = Thm.equal_elim eq_th type_definition

    (* instantiate Abs_inverse rule *)
    val instT = [((("'a", 0), typeS), certT newT),
                 ((("'b", 0), typeS), certT oldT)]
    val inst = [((("Rep", 0), RepT), cert RepC),
                ((("Abs", 0), AbsT), cert AbsC),
                ((("P", 0), phiT), cert phi),
                ((("r", 0), oldT), cert (Free ("r", oldT)))]

    val rule = Thm.instantiate (instT, inst) @{thm type_definition_Collect_iff}
    val rep_abs = un_meta(Thm.abstract_rule "r" (cert (Free ("r", oldT))) 
                                     (Thm.symmetric(mk_meta(Thm.implies_elim rule type_definition))))
  in
    ((tyop, Abs_name, Rep_name, abs_rep, rep_abs), thy)
  end






fun alpha (th : thm) ts t : thm =
  let
    val _ = writeln
      (if null ts
       then print_cterm t
       else print_cterm t ^ " " ^ ML_Syntax.print_list print_cterm ts)
  in
    Thm.equal_elim (Thm.reflexive (mk_prop t)) th
  end

fun iff_intro th1 (*P*) th2 (*Q*) : thm (*P=Q*) =
  let
    val cprop1 = Thm.cprop_of th1
    val cprop2 = Thm.cprop_of th2
    val th1 (*Q->P*) = Thm.implies_intr cprop2 th1
    val th2 (*P->Q*) = Thm.implies_intr cprop1 th2

    (* Instantiate iffI rule *)
    val P = un_prop cprop1
    val Q = un_prop cprop2
    val rule = Thm.instantiate ([], [((("P", 0), HOLogic.boolT), P), 
                                     ((("Q", 0), HOLogic.boolT), Q)]) iffI

    val th3 = Thm.implies_elim (Thm.implies_elim rule th2) th1

    (* Correctness check *)
    val P = HOLogic.dest_Trueprop (Thm.term_of cprop1)
    val Q = HOLogic.dest_Trueprop (Thm.term_of cprop2)
    val PQ = HOLogic.dest_Trueprop (Thm.concl_of th3)
    val PQ' = HOLogic.mk_eq (P, Q)
    val _ = if PQ aconv PQ' then () else internal_err "iff_intro"
  in
    th3
  end

(* Thm.generalize doesn't distinguish similarly-named free variables
with the same type. We will use forall_intr/forall_elim instead. *)
fun subst (ts : (var * trm) list) (tys : (string * typ) list) th (thy:theory) : thm =
  let
    (* Convert hyps to implication *)
    val th = Drule.implies_intr_list (Thm.chyps_of th) th

    (* Substitute type variables *)
    val tfrees = map (prime o fst) tys
    val idx = Thm.maxidx_of th + 1
    val th = Thm.generalize (tfrees, []) idx th
        handle THM (s, _, _) => internal_err ("subst/generalize: " ^ s)
    val certT = Thm.global_ctyp_of thy
    val instT = map (fn (a, ty) => (((prime a, idx), typeS), certT ty)) tys
    val th = Thm.instantiate (instT, []) th
        handle THM (s, _, _) => internal_err ("subst/instantiate: " ^ s)

    (* Substitute term variables *)
    val (xs, ys) = ListPair.unzip ts
    val th = fold Thm.forall_intr xs th
    val th = fold_rev Thm.forall_elim ys th

    (* Convert implications back into hyps *)
    val prems = Drule.strip_imp_prems (Thm.cprop_of th)
    val th = Drule.implies_elim_list th (map Thm.assume prems)
  in
    th
  end




(* proveHyp command in Version 6 *) 
fun prove_hyp psi phi =
  let val c = Thm.cprop_of phi  (* or Thm.dest_arg(Thm.cprop_of phi)? *)
      val psi' = Thm.implies_intr c psi
  in
   Thm.implies_elim psi' phi
  end


(* sym command in Version 6 *)
val sym = un_meta o Thm.symmetric o mk_meta 

(* trans command in Version 6 : Thm.transitive should take care of
   alpha-equivalence *)
fun trans th1 th2 = un_meta (Thm.transitive (mk_meta th1) (mk_meta th2))

(** Parsing commands **)

datatype command
  = CComment of string
  | CNum of int
  | CName of string
  | CDef
  | CRef
  | CRemove
  | CPop
  | CNil
  | CCons

  (* types and terms *)
  | CTypeOp
  | CVarType
  | COpType
  | CConst
  | CVar
  | CConstTerm
  | CVarTerm
  | CAbsTerm
  | CAppTerm
  (* logical inferences *)
  | CAxiom
  | CAssume
  | CAbsThm
  | CAppThm
  | CBetaConv
  | CRefl
  | CSubst
  | CDeductAntisym
  | CEqMp
  | CDefineConst
  | CDefineTypeOp
  | CThm

(* Version 6 *)
  | CHdTl
  | CVersion
  | CPragma
  | CProveHyp
  | CSym
  | CTrans
  | CDefConstList
(* *** *)



val cmd_table =
  [("absTerm", CAbsTerm),
   ("absThm", CAbsThm),
   ("appTerm", CAppTerm),
   ("appThm", CAppThm),
   ("assume", CAssume),
   ("axiom", CAxiom),
   ("betaConv", CBetaConv),
   ("cons", CCons),
   ("const", CConst),
   ("constTerm", CConstTerm),
   ("deductAntisym", CDeductAntisym),
   ("def", CDef),
   ("defineConst", CDefineConst),
   ("defineTypeOp", CDefineTypeOp),
   ("eqMp", CEqMp),
   ("nil", CNil),
   ("opType", COpType),
   ("pop", CPop),
   ("ref", CRef),
   ("refl", CRefl),
   ("remove", CRemove),
   ("subst", CSubst),
   ("thm", CThm),
   ("typeOp", CTypeOp),
   ("var", CVar),
   ("varTerm", CVarTerm),
   ("varType", CVarType),
   ("hdTl", CHdTl),
   ("pragma", CPragma),
   ("proveHyp", CProveHyp),
   ("sym", CSym),
   ("trans", CTrans),
   ("version", CVersion),
   ("defineConstList", CDefConstList)]


fun lookupC _ [] = internal_err "command not listed"
  | lookupC c ((s, com)::xs) = (if c = com then s else lookupC c xs) 


(*
val cmd_table : command Symtab.table =
  Symtab.make
  [("absTerm", CAbsTerm),
   ("absThm", CAbsThm),
   ("appTerm", CAppTerm),
   ("appThm", CAppThm),
   ("assume", CAssume),
   ("axiom", CAxiom),
   ("betaConv", CBetaConv),
   ("cons", CCons),
   ("const", CConst),
   ("constTerm", CConstTerm),
   ("deductAntisym", CDeductAntisym),
   ("def", CDef),
   ("defineConst", CDefineConst),
   ("defineTypeOp", CDefineTypeOp),
   ("eqMp", CEqMp),
   ("nil", CNil),
   ("opType", COpType),
   ("pop", CPop),
   ("ref", CRef),
   ("refl", CRefl),
   ("remove", CRemove),
   ("subst", CSubst),
   ("thm", CThm),
   ("typeOp", CTypeOp),
   ("var", CVar),
   ("varTerm", CVarTerm),
   ("varType", CVarType)]
*)

local open Substring in
  val trimlr = fn s => string(trimr 1 (triml 1 (full s)))
end

fun parse s =
  let
    val c = String.sub(s,0)
    open Char Option Int
  in
    if isDigit c then CNum (valOf (fromString s)) else
    if c = #"\"" then CName (trimlr s) else
    if c = #"#" then CComment s else
(*
    case Symtab.lookup cmd_table s of
      SOME com => com
    | NONE => raise ERR ("Parse error: unknown command " ^ s)
*)
    case s of
      "ref" => CRef
    | "cons" => CCons
    | "nil" => CNil
    | "def" => CDef
    | "remove" => CRemove
    | "appTerm" => CAppTerm
    | "eqMp" => CEqMp
    | "subst" => CSubst
    | "appThm" => CAppThm
    | "deductAntisym" => CDeductAntisym
    | "absTerm" => CAbsTerm
    | "refl" => CRefl
    | "betaConv" => CBetaConv
    | "absThm" => CAbsThm
    | "var" => CVar
    | "opType" => COpType
    | "varTerm" => CVarTerm
    | "constTerm" => CConstTerm
    | "assume" => CAssume
    | "axiom" => CAxiom
    | "thm" => CThm
    | "pop" => CPop
    | "const" => CConst
    | "defineConst" => CDefineConst
    | "varType" => CVarType
    | "typeOp" => CTypeOp
    | "defineTypeOp" => CDefineTypeOp
(* Version 6 *)
    | "version" => CVersion
    | "hdTl" => CHdTl
    | "pragma" => CPragma
    | "proveHyp" => CProveHyp
    | "sym" => CSym
    | "trans" => CTrans
    | "defineConstList" => CDefConstList
    | _ => raise ERR ("Parse error: unknown command " ^ s)
  end


(** Executing commands **)

datatype object
  = ONum of int
  | OName of string
  | OList of object list
  | OTypeOp of tyop
  | OType of typ
  | OConst of const
  | OVar of var
  | OTerm of trm
  | OThm of thm

val dest_OTerm =
    (fn OTerm t => t | _ => internal_err "dest_OTerm")

val dest_OType =
    (fn OType ty => ty | _ => internal_err "dest_OType")

val dest_OName =
    (fn OName n => n | _ => internal_err "dest_OName")

val dest_OName_OType =
    (fn OList [OName a, OType t] => (a, t)
      | _ => internal_err "dest_OName_OType")

val dest_OVar_OTerm =
    (fn OList [OVar v, OTerm t] => (v, t)
      | _ => internal_err "dest_OVar_OTerm")

fun raw_read_article
      (path : Path.T)
      (renaming : (string * string) list)
      (thy0 : theory) : theory =
  let
    (* Theory data references *)
    val thms_net = OT_Thms.get (Context.Theory thy0)
    val consts_tab = OT_Consts.get thy0
    val tyops_tab = OT_TyOps.get thy0

    (* User-supplied renamings for new constants and types *)
    fun rename s = the_default s (AList.lookup (op =) renaming s)

    fun find_const s =
        case Symtab.lookup consts_tab s of
          SOME s' => s'
        | NONE => raise ERR ("No translation for const: " ^ s)

    fun find_tyop s =
        case Symtab.lookup tyops_tab s of
          SOME s' => s'
        | NONE => raise ERR ("No translation for tyop: " ^ s)

    fun step command (st as {stack, dict, thy:theory, version:int}) =
      let
        fun st_ stack' = {stack=stack', dict=dict, thy=thy, version=version}

        fun find k =
          case Inttab.lookup dict k of
            SOME x => x | NONE => internal_err "dictionary lookup failed"

        fun f _ (CNum i) os = st_ (ONum i :: os)
          | f _ (CName n) os = st_ (OName (rename n) :: os)
          | f _ (CComment _) _ = st
          | f _ CDef (ONum k :: x :: os) =
              {stack = x :: os, dict = Inttab.update (k, x) dict, thy = thy, version = version}
          | f _ CRef (ONum k :: os) = st_ (find k :: os)
          | f _ CRemove (ONum k :: os) =
              {stack = find k :: os, dict = Inttab.delete k dict, thy = thy, version = version}
          | f _ CPop (_ :: os) = st_ (os)
          | f _ CNil os = st_ (OList [] :: os)
          | f _ CCons (OList t :: h :: os) = st_ (OList (h :: t) :: os)

          (* types and terms *)
          | f _ CTypeOp (OName n :: os) =
            st_ (OTypeOp (find_tyop n) :: os)
          | f _ CVarType (OName n :: os) =
            st_ (OType (Term.TFree (prime n, typeS)) :: os)
          | f _ COpType (OList ls :: OTypeOp tyop :: os) =
            st_ (OType (Term.Type (tyop, map dest_OType ls)) :: os)
          | f _ CConst (OName n :: os) =
            st_ (OConst (find_const n) :: os)
          | f _ CVar (OType ty :: OName n :: os) =
            st_ (OVar (Thm.global_cterm_of thy (Free (n, ty))) :: os)
          | f _ CConstTerm (OType ty :: OConst c :: os) =
              st_ (OTerm (Thm.global_cterm_of thy (Const (c, ty))) :: os)
          | f _ CVarTerm (OVar t :: os) = st_ (OTerm t :: os)
          | f _ CAbsTerm (OTerm b :: OVar v :: os) = st_ (OTerm (Thm.lambda v b) :: os)
          | f _ CAppTerm (OTerm x :: OTerm f :: os) = st_ (OTerm (Thm.apply f x) :: os)

          (* logical inferences *)
          | f _ CAxiom (OTerm t :: OList ts :: os) =
             let val (thm, thy') = find_thm thms_net (map dest_OTerm ts) t thy
             in
               {stack = OThm thm :: os, dict = dict, thy = thy', version = version}
             end
          | f _ CAssume (OTerm t :: os) = st_ (OThm (assume t) :: os)
          | f _ CAbsThm (OThm th :: OVar v :: os) = st_ (OThm (abs_thm v th) :: os)
          | f _ CAppThm (OThm xy :: OThm fg :: os) = st_ (OThm (app_thm fg xy) :: os)
          | f _ CBetaConv (OTerm t :: os) = st_ (OThm (beta_conv t) :: os)
          | f _ CRefl (OTerm t::os) = st_ (OThm (refl t) :: os)
          | f _ CSubst (OThm th :: OList [OList tys, OList tms] :: os) =
            let
              val tys = map dest_OName_OType tys
              val tms = map dest_OVar_OTerm tms
              val th' = subst tms tys th thy
            in st_ (OThm th' :: os) end
          | f _ CDeductAntisym (OThm t2 :: OThm t1 :: os) =
            st_ (OThm (iff_intro t1 t2) :: os)
          | f _ CEqMp (OThm f :: OThm fg :: os) =
            st_ (OThm (iff_elim fg f) :: os)
          | f _ CDefineConst (OTerm t :: OName n :: os) =
            let
              val ((const, def), thy') = define_const n t thy NONE (* consts_tab *)
            in
              {stack = OThm def :: OConst const :: os, dict = dict, thy = thy', version = version}
            end
          | f v CDefineTypeOp
              (OThm ax :: OList ls :: OName rep :: OName abs :: OName n :: os) =
            let
              val ls = map dest_OName ls
              val the_define_tyop = (case v of
                      5 => define_tyop
                    | 6 => define_tyop6
                    | v => raise ERR ("Unknown version for defineTypeOp: " ^ string_of_int v))
              val ((tyop, abs, rep, abs_rep, rep_abs), thy') = the_define_tyop n abs rep ls ax thy
            in
              {stack = OThm rep_abs :: OThm abs_rep ::
                       OConst rep :: OConst abs ::
                       OTypeOp tyop :: os,
               dict = dict, thy = thy', version = version}
            end
          | f _ CThm (OTerm c :: OList ls :: OThm th :: os) =
            let
              val th' = alpha th (map dest_OTerm ls) c
              val thy' = Context.theory_map (Option.valOf o fst o add_thm o rpair th') thy
            in
              {stack = os, dict = dict, thy = thy', version = version}
            end

          (* Version 6 *)
          | f _ CVersion (ONum v :: os) = {stack=os, dict=dict, thy=thy, version=v}

          | f 6 CHdTl (OList (h :: t) :: os) = st_ (OList t :: h :: os)

          | f 6 CPragma (OName x :: os) = (let val _ = if x = "debug" then writeln "Some debug info..."
                                                     else ()
                                         in  {stack = os, dict = dict, thy = thy, version = version} end)
          | f 6 CProveHyp (OThm psi :: OThm phi :: os) =
                st_ (OThm (prove_hyp psi phi) ::os)

          | f 6 CSym (OThm phi :: os) =
               st_ (OThm (sym phi) ::os)

          | f 6 CTrans (OThm psi :: OThm phi :: os) =
                st_ (OThm (trans phi psi) ::os)

          | f 6 CDefConstList (OThm phi :: OList ls :: os) =
             let fun lookupT v [] = internal_err ("defineConstList: no def name for the variable "^(fst v))
                   | lookupT v ((x, t)::xs) = (if x = v then t else lookupT v xs)
                 val hyps = Thm.hyps_of phi

                 fun dest_eq (ct as (Const ("HOL.Trueprop", _) $ (Const ("HOL.eq", _) $ (Free(x, s)) $ t))) = 
                      ((x, s), (t, Thm.global_cterm_of thy ct))
                   | dest_eq t = raise TERM ("defineConstList: dest_eq -- ", [t])

                 val asgs = map dest_eq hyps
                 fun proc_def_asgs [] = []
                   | proc_def_asgs (OList [OName n, OVar v]::xs) = 
                      (case Thm.term_of v of
                        Free(x, s) => (x, s, n, lookupT (x, s) asgs)::proc_def_asgs xs
                      | _ => internal_err "defineConstList: unexpected OVar")
                   | proc_def_asgs _ = internal_err "defineConstList: unexpected content of OList"
                 val ext_asgs = proc_def_asgs ls
                 fun proc_ext_asgs thy th consts [] = (thy, th, consts)
                   | proc_ext_asgs thy th consts ((x, _, n, (t, hyp))::xs) =
                       let val rhs = Thm.global_cterm_of thy t
                           val ((c, def), thy') = define_const n rhs thy NONE
                           val _ = writeln("constant " ^ n ^ " defined as " ^ Syntax.string_of_term_global thy' t)
                           val ty = Thm.typ_of_cterm rhs
                           val ct = Thm.global_cterm_of thy' (Const(c, ty))
                           val th' = Thm.implies_intr hyp th
                           val idx = Thm.maxidx_of th' + 1
                           val th'' = Thm.generalize ([], [x]) idx th'
                           val th3 = Drule.instantiate_normalize ([], [(((x, idx), ty), ct)]) th''
                           val th4 = Thm.implies_elim th3 def
                       in
                        proc_ext_asgs thy' th4 (consts @ [OConst c]) xs
                       end 
                 val (thy', phi', consts) = proc_ext_asgs thy phi [] ext_asgs
             in
              {stack = OThm phi' :: OList consts :: os, dict = dict, thy = thy', version = version}
             end
          | f v c _ = internal_err ("Version " ^ string_of_int v ^ ": illegal stack configuration for the command " ^
                                   (lookupC c cmd_table))
      in
        f version command stack
      end

    fun handler i msg =
        error ("Error on line " ^ ML_Syntax.print_int i ^ ":\n" ^ msg)

  in
    File.fold_lines
      (fn line => fn (i, x) =>
        let
          val x' = (step (parse line) x handle ERR s => handler i s)
        in
          (i+1, x')
        end
      )
      path
      (1, {stack = [], dict = Inttab.empty, thy =  thy0, version = 5})
    |> #2
    |> #thy
  end


fun read_article filepath renames thy =
  raw_read_article (Path.append (Resources.master_directory thy) (Path.explode filepath)) renames thy

end
