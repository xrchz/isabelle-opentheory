(* opentheory.ML *)
(* version: Isabelle 2011 *)

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
in
val add_thm =
  Thm.declaration_attribute (fn th => OT_Thms.map (Termtab.update (key_of th, th)))
val del_thm =
  Thm.declaration_attribute (fn th => OT_Thms.map (Termtab.delete (key_of th)))
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
fun mk_prop t = Thm.capply @{cterm Trueprop} t
fun un_prop t = Thm.dest_arg t

(* = <-> == *)
fun mk_meta th =
  let
    val thy = Thm.theory_of_thm th
    val xy = un_prop (Thm.cprop_of th)
    val x = Thm.dest_arg1 xy
    val y = Thm.dest_arg xy
    val a = Thm.ctyp_of_term x
    val T = Thm.typ_of a
    val ca = Thm.ctyp_of thy (TVar (("'a", 0), typeS))
    val cx = Thm.cterm_of thy (Var (("x", 0), T))
    val cy = Thm.cterm_of thy (Var (("y", 0), T))
    val rule = Thm.instantiate ([(ca, a)], [(cx, x), (cy, y)]) eq_reflection
    val th' = Thm.implies_elim rule th
    val (x', y') = Logic.dest_equals (Thm.concl_of th')
    val _ = if (Thm.term_of x) aconv x' then () else internal_err "mk_meta"
    val _ = if (Thm.term_of y) aconv y' then () else internal_err "mk_meta"
  in
    th'
  end

fun un_meta th =
  let
    val thy = Thm.theory_of_thm th
    val xy = Thm.cprop_of th
    val x = Thm.dest_arg1 xy
    val y = Thm.dest_arg xy
    val a = Thm.ctyp_of_term x
    val T = Thm.typ_of a
    val ca = Thm.ctyp_of thy (TVar (("'a", 0), typeS))
    val cx = Thm.cterm_of thy (Var (("A", 0), T))
    val cy = Thm.cterm_of thy (Var (("B", 0), T))
    val rule = Thm.instantiate ([(ca, a)], [(cx, x), (cy, y)]) meta_eq_to_obj_eq
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

(*fun app_thm th1 th2 = @{thm cong} OF [th1, th2]*)
fun app_thm th1 th2 =
  let
    val th3 = un_meta (Thm.combination (mk_meta th1) (mk_meta th2))

    (* Correctness check *)
    val (f, g) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.concl_of th1))
    val (x, y) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.concl_of th2))
    val eq1 = HOLogic.dest_Trueprop (Thm.concl_of th3)
    val eq2 = HOLogic.mk_eq (f $ x, g $ y)
    val _ = if eq1 aconv eq2 then () else internal_err "app_thm"
  in
    th3
  end

fun beta_conv t = un_meta (Thm.beta_conversion false t)
fun refl t = un_meta (Thm.reflexive t)

(* lookup in translation tables *)
fun find_thm tab ts t : thm =
  let
    (* FIXME: should sort ts first? *)
    val prop = Drule.list_implies (map mk_prop ts, mk_prop t)
    val ths = Termtab.lookup tab (Thm.term_of prop)
  in
    case ths of
      NONE => raise ERR ("missing axiom: " ^
        ML_Syntax.print_list print_cterm ts ^ " |- " ^ print_cterm t)
    | SOME th => th
  end

fun iff_elim th1 (*Q=P*) th2 (*Q*) : thm (*P*) =
  let
    val cQ = @{cpat "?Q::bool"}
    val cP = @{cpat "?P::bool"}
    val QP = Thm.dest_arg (Thm.cprop_of th1)
    val Q = Thm.dest_arg1 QP
    val P = Thm.dest_arg QP
    val Q' = Thm.dest_arg (Thm.cprop_of th2)
    val _ = if (Thm.term_of Q) aconv (Thm.term_of Q')
            then () else internal_err "iff_elim"
    val rule = Thm.instantiate ([], [(cQ, Q), (cP, P)]) iffD1
    val th3 = Thm.implies_elim (Thm.implies_elim rule th1) th2

    (* Correctness check *)
    val PQ = HOLogic.dest_Trueprop (Thm.concl_of th1)
    val P = HOLogic.dest_Trueprop (Thm.concl_of th2)
    val Q = HOLogic.dest_Trueprop (Thm.concl_of th3)
    val PQ' = HOLogic.mk_eq (P, Q)
    val _ = if PQ aconv PQ' then () else internal_err "iff_elim"
  in
    th3
  end

fun define_const
    (s : string)
    (rhs : trm)
    (thy : theory)
  : (const * thm) * theory =
  let
    val bind = Binding.qualified_name s (* FIXME: do proper name translation *)
    val typ = Thm.typ_of (Thm.ctyp_of_term rhs)
    val _ = writeln (s ^ " :: " ^ Syntax.string_of_typ_global thy typ)
    val (lhs, thy) = Sign.declare_const ((bind, typ), NoSyn) thy
    val eqn = Logic.mk_equals (lhs, Thm.term_of rhs)
    val def = Thm.no_attributes (Binding.suffix_name "_def" bind, eqn)
    val (def_thm, thy) = yield_singleton (Global_Theory.add_defs false) def thy
    val def_thm = Thm.legacy_freezeT def_thm
    (* TODO: Correctness check *)
    (* def_thm might be incorrect if rhs is not beta-normal *)
    val const = fst (dest_Const lhs)
    (* register constant name in database *)
    val thy = add_const (s, const) thy
  in
    ((const, un_meta def_thm), thy)
  end

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
    val tac = EVERY' [rtac exI, rtac CollectI, rtac ax] 1
    val ((tyop, ({Rep_name, Abs_name, ...}, info)), thy) =
        Typedef.add_typedef_global false NONE typ set morphs tac thy
    val {type_definition, Rep_inverse, ...} = info

    (* instantiate Rep_inverse rule *)
    val certT = Thm.ctyp_of thy
    val cert = Thm.cterm_of thy
    val tfrees = map (fn a => TFree (a, typeS)) args'
    val tvars = map (fn a => TVar ((a, 0), typeS)) args'
    val newT = Type (tyop, tfrees)
    val instT = map2 (fn x => fn y => (certT x, certT y)) tvars tfrees
    val inst = [(cert (Var (("x", 0), newT)), cert (Free ("a", newT)))]
    val abs_rep = Thm.instantiate (instT, inst) Rep_inverse

    (* rebuild non-normalized type_definition rule *)
    val type_definition = Thm.instantiate (instT, []) type_definition
    val RepT = newT --> oldT
    val AbsT = oldT --> newT
    val phiT = oldT --> HOLogic.boolT
    val RepC = Const (Rep_name, RepT)
    val AbsC = Const (Abs_name, AbsT)
    val typedefT = RepT --> AbsT --> phiT --> HOLogic.boolT
    val typedefC = Const (@{const_name type_definition}, typedefT)
    val cprop = cert (HOLogic.mk_Trueprop (typedefC $ RepC $ AbsC $ set))
    val eq_th = Thm.symmetric (Thm.beta_conversion true cprop)
    val type_definition = Thm.equal_elim eq_th type_definition

    (* instantiate Abs_inverse rule *)
    val instT = [(certT (TVar (("'a", 0), typeS)), certT newT),
                 (certT (TVar (("'b", 0), typeS)), certT oldT)]
    val inst = [(cert (Var (("Rep", 0), RepT)), cert RepC),
                (cert (Var (("Abs", 0), AbsT)), cert AbsC),
                (cert (Var (("P", 0), phiT)), cert phi),
                (cert (Var (("r", 0), oldT)), cert (Free ("r", oldT)))]
    val rule = Thm.instantiate (instT, inst) @{thm type_definition_Collect_iff}
    val rep_abs = Thm.implies_elim rule type_definition
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
    val cP = @{cpat "?P::bool"}
    val cQ = @{cpat "?Q::bool"}
    val P = un_prop cprop1
    val Q = un_prop cprop2
    val rule = Thm.instantiate ([], [(cP, P), (cQ, Q)]) iffI
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
fun subst (ts : (var * trm) list) (tys : (string * typ) list) th thy : thm =
  let
    (* Convert hyps to implication *)
    val th = Drule.implies_intr_list (#hyps (crep_thm th)) th

    (* Substitute type variables *)
    val tfrees = map (prime o fst) tys
    val idx = Thm.maxidx_of th + 1
    val th = Thm.generalize (tfrees, []) idx th
        handle THM (s, _, _) => internal_err ("subst/generalize: " ^ s)
    val certT = Thm.ctyp_of thy
    val instT = map (fn (a, ty) => (certT (TVar ((prime a, idx), typeS)), certT ty)) tys
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

local open Substring in
  val trimlr = fn s => string(trimr 1 (triml 1 (full s)))
  val trimr  = fn s => string(trimr 1 (full s))
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
      (input : TextIO.instream)
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

    fun step command (st as {stack, dict, thy}) =
      let
        fun st_ stack' = {stack=stack', dict=dict, thy=thy}

        fun find k =
          case Inttab.lookup dict k of
            SOME x => x | NONE => internal_err "dictionary lookup failed"

        fun f (CNum i) os = st_ (ONum i :: os)
          | f (CName n) os = st_ (OName (rename n) :: os)
          | f (CComment _) _ = st
          | f CDef (ONum k :: x :: os) =
              {stack = x :: os, dict = Inttab.update (k, x) dict, thy = thy}
          | f CRef (ONum k :: os) = st_ (find k :: os)
          | f CRemove (ONum k :: os) =
              {stack = find k :: os, dict = Inttab.delete k dict, thy = thy}
          | f CPop (_ :: os) = st_ (os)
          | f CNil os = st_ (OList [] :: os)
          | f CCons (OList t :: h :: os) = st_ (OList (h :: t) :: os)

          (* types and terms *)
          | f CTypeOp (OName n :: os) =
            st_ (OTypeOp (find_tyop n) :: os)
          | f CVarType (OName n :: os) =
            st_ (OType (Term.TFree (prime n, typeS)) :: os)
          | f COpType (OList ls :: OTypeOp tyop :: os) =
            st_ (OType (Term.Type (tyop, map dest_OType ls)) :: os)
          | f CConst (OName n :: os) =
            st_ (OConst (find_const n) :: os)
          | f CVar (OType ty :: OName n :: os) =
            st_ (OVar (Thm.cterm_of thy (Free (n, ty))) :: os)
          | f CConstTerm (OType ty :: OConst c :: os) =
            st_ (OTerm (Thm.cterm_of thy (Const (c, ty))) :: os)
          | f CVarTerm (OVar t :: os) = st_ (OTerm t :: os)
          | f CAbsTerm (OTerm b :: OVar v :: os) = st_ (OTerm (Thm.cabs v b) :: os)
          | f CAppTerm (OTerm x :: OTerm f :: os) = st_ (OTerm (Thm.capply f x) :: os)

          (* logical inferences *)
          | f CAxiom (OTerm t :: OList ts :: os) =
            st_ (OThm (find_thm thms_net (map dest_OTerm ts) t) :: os)
          | f CAssume (OTerm t :: os) = st_ (OThm (assume t) :: os)
          | f CAbsThm (OThm th :: OVar v :: os) = st_ (OThm (abs_thm v th) :: os)
          | f CAppThm (OThm xy :: OThm fg :: os) = st_ (OThm (app_thm fg xy) :: os)
          | f CBetaConv (OTerm t :: os) = st_ (OThm (beta_conv t) :: os)
          | f CRefl (OTerm t::os) = st_ (OThm (refl t) :: os)
          | f CSubst (OThm th :: OList [OList tys, OList tms] :: os) =
            let
              val tys = map dest_OName_OType tys
              val tms = map dest_OVar_OTerm tms
              val th' = subst tms tys th thy
            in st_ (OThm th' :: os) end
          | f CDeductAntisym (OThm t2 :: OThm t1 :: os) =
            st_ (OThm (iff_intro t1 t2) :: os)
          | f CEqMp (OThm f :: OThm fg :: os) =
            st_ (OThm (iff_elim fg f) :: os)
          | f CDefineConst (OTerm t :: OName n :: os) =
            let
              val ((const, def), thy') = define_const n t thy
            in
              {stack = OThm def :: OConst const :: os, dict = dict, thy = thy'}
            end
          | f CDefineTypeOp
              (OThm ax :: OList ls :: OName rep :: OName abs :: OName n :: os) =
            let
              val ls = map dest_OName ls
              val ((tyop, abs, rep, abs_rep, rep_abs), thy') =
                  define_tyop n abs rep ls ax thy
            in
              {stack = OThm rep_abs :: OThm abs_rep ::
                       OConst rep :: OConst abs ::
                       OTypeOp tyop :: os,
               dict = dict, thy = thy'}
            end
          | f CThm (OTerm c :: OList ls :: OThm th :: os) =
            let
              val th' = alpha th (map dest_OTerm ls) c
              val thy' = Context.theory_map (fst o add_thm o rpair th') thy
            in
              {stack = os, dict = dict, thy = thy'}
            end
          | f _ _ = internal_err "illegal stack configuration"
      in
        f command stack
      end

    fun handler i msg =
        error ("Error on line " ^ ML_Syntax.print_int i ^ ":\n" ^ msg)

    fun loop i x =
      case TextIO.inputLine input of
        NONE => x before TextIO.closeIn(input)
      | SOME line =>
        let
          val x' = (step (parse (trimr line)) x handle ERR s => handler i s)
        in
          loop (i+1) x'
        end
  in
    #thy (loop 1 {stack = [], dict = Inttab.empty, thy = Theory.copy thy0})
  end

fun read_article filepath = raw_read_article (TextIO.openIn filepath)

end
