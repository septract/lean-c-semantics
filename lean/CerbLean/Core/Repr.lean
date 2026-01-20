/-
  Repr instances for Core AST types

  These enable serializing the AST back to valid Lean source code,
  which is useful for generating standalone proof files.
-/

import CerbLean.Core.File

namespace CerbLean.Core

-- Helper for formatting lists
private def reprList (items : List Std.Format) : Std.Format :=
  .text "[" ++ .group (.nest 2 (.join (items.map (· ++ .text ", ")))) ++ .text "]"

-- Helper to wrap repr output in parentheses (needed for types with constructors that take arguments)
private def reprParen [Repr α] (x : α) : Std.Format :=
  .text "(" ++ repr x ++ .text ")"

-- Forward declarations for mutual recursion
mutual
  partial def reprExpr : Expr → Std.Format
    | .pure e => Std.Format.group (.text ".pure " ++ reprAPexpr e)
    | .memop op args =>
      .group (.text ".memop " ++ repr op ++ .text " " ++ reprAPexprList args)
    | .action a => .group (.text ".action " ++ reprPaction a)
    | .case_ scrut branches =>
      .group (.text ".case_ " ++ reprAPexpr scrut ++ .text " " ++
        reprList (branches.map fun (p, e) => .group (.text "(" ++ reprAPattern p ++ .text ", " ++ reprAExpr e ++ .text ")")))
    | .let_ pat e1 e2 =>
      .group (.text ".let_ " ++ reprAPattern pat ++ .text " " ++ reprAPexpr e1 ++ .text " " ++ reprAExpr e2)
    | .if_ cond then_ else_ =>
      .group (.text ".if_ " ++ reprAPexpr cond ++ .text " " ++ reprAExpr then_ ++ .text " " ++ reprAExpr else_)
    | .ccall funPtr funTy args =>
      .group (.text ".ccall " ++ reprAPexpr funPtr ++ .text " " ++ reprAPexpr funTy ++ .text " " ++ reprAPexprList args)
    | .proc name args =>
      .group (.text ".proc " ++ repr name ++ .text " " ++ reprAPexprList args)
    | .unseq es => .group (.text ".unseq " ++ reprAExprList es)
    | .wseq pat e1 e2 =>
      .group (.text ".wseq " ++ reprAPattern pat ++ .text " " ++ reprAExpr e1 ++ .text " " ++ reprAExpr e2)
    | .sseq pat e1 e2 =>
      .group (.text ".sseq " ++ reprAPattern pat ++ .text " " ++ reprAExpr e1 ++ .text " " ++ reprAExpr e2)
    | .bound e => .group (.text ".bound " ++ reprAExpr e)
    | .nd es => .group (.text ".nd " ++ reprAExprList es)
    | .save retSym retTy args body =>
      .group (.text ".save " ++ repr retSym ++ .text " " ++ reprParen retTy ++ .text " " ++
        reprList (args.map fun (s, t, e) => .group (.text "(" ++ repr s ++ .text ", " ++ reprParen t ++ .text ", " ++ reprAPexpr e ++ .text ")")) ++
        .text " " ++ reprAExpr body)
    | .run label args =>
      .group (.text ".run " ++ repr label ++ .text " " ++ reprAPexprList args)
    | .par es => .group (.text ".par " ++ reprAExprList es)
    | .wait tid => .group (.text ".wait " ++ repr tid)

  partial def reprAExpr (e : AExpr) : Std.Format :=
    .group (.text "{ annots := " ++ repr e.annots ++ .text ", expr := " ++ reprExpr e.expr ++ .text " }")

  partial def reprAExprList (es : List AExpr) : Std.Format :=
    reprList (es.map reprAExpr)

  partial def reprAPexpr (e : APexpr) : Std.Format :=
    .group (.text "{ annots := " ++ repr e.annots ++ .text ", ty := " ++ reprParen e.ty ++
            .text ", expr := " ++ reprPexpr e.expr ++ .text " }")

  partial def reprAPexprList (es : List APexpr) : Std.Format :=
    .text "[" ++ .group (.nest 2 (.join (es.map fun e => reprAPexpr e ++ .text ", "))) ++ .text "]"

  partial def reprPexpr : Pexpr → Std.Format
    | .sym s => .group (.text "(.sym " ++ repr s ++ .text ")")
    | .impl c => .group (.text "(.impl " ++ repr c ++ .text ")")
    | .val v => .group (.text "(.val " ++ reprValue v ++ .text ")")
    | .undef loc ub => .group (.text "(.undef " ++ reprParen loc ++ .text " " ++ repr ub ++ .text ")")
    | .error msg e => .group (.text "(.error " ++ repr msg ++ .text " " ++ reprPexpr e ++ .text ")")
    | .ctor c args => .group (.text "(.ctor " ++ repr c ++ .text " " ++ reprPexprList args ++ .text ")")
    | .case_ scrut branches =>
      .group (.text "(.case_ " ++ reprPexpr scrut ++ .text " " ++
        reprList (branches.map fun (p, e) => .group (.text "(" ++ reprAPattern p ++ .text ", " ++ reprPexpr e ++ .text ")")) ++ .text ")")
    | .arrayShift ptr ty idx =>
      .group (.text "(.arrayShift " ++ reprPexpr ptr ++ .text " " ++ reprParen ty ++ .text " " ++ reprPexpr idx ++ .text ")")
    | .memberShift ptr tag member =>
      .group (.text "(.memberShift " ++ reprPexpr ptr ++ .text " " ++ repr tag ++ .text " " ++ repr member ++ .text ")")
    | .not_ e => .group (.text "(.not_ " ++ reprPexpr e ++ .text ")")
    | .op op e1 e2 => .group (.text "(.op " ++ repr op ++ .text " " ++ reprPexpr e1 ++ .text " " ++ reprPexpr e2 ++ .text ")")
    | .struct_ tag members =>
      .group (.text "(.struct_ " ++ repr tag ++ .text " " ++
        reprList (members.map fun (id, e) => .group (.text "(" ++ repr id ++ .text ", " ++ reprPexpr e ++ .text ")")) ++ .text ")")
    | .union_ tag member value =>
      .group (.text "(.union_ " ++ repr tag ++ .text " " ++ repr member ++ .text " " ++ reprPexpr value ++ .text ")")
    | .cfunction e => .group (.text "(.cfunction " ++ reprPexpr e ++ .text ")")
    | .memberof tag member e =>
      .group (.text "(.memberof " ++ repr tag ++ .text " " ++ repr member ++ .text " " ++ reprPexpr e ++ .text ")")
    | .call name args => .group (.text "(.call " ++ reprParen name ++ .text " " ++ reprPexprList args ++ .text ")")
    | .let_ pat e1 e2 =>
      .group (.text "(.let_ " ++ reprAPattern pat ++ .text " " ++ reprPexpr e1 ++ .text " " ++ reprPexpr e2 ++ .text ")")
    | .if_ cond then_ else_ =>
      .group (.text "(.if_ " ++ reprPexpr cond ++ .text " " ++ reprPexpr then_ ++ .text " " ++ reprPexpr else_ ++ .text ")")
    | .isScalar e => .group (.text "(.isScalar " ++ reprPexpr e ++ .text ")")
    | .isInteger e => .group (.text "(.isInteger " ++ reprPexpr e ++ .text ")")
    | .isSigned e => .group (.text "(.isSigned " ++ reprPexpr e ++ .text ")")
    | .isUnsigned e => .group (.text "(.isUnsigned " ++ reprPexpr e ++ .text ")")
    | .areCompatible e1 e2 => .group (.text "(.areCompatible " ++ reprPexpr e1 ++ .text " " ++ reprPexpr e2 ++ .text ")")
    | .convInt ty e => .group (.text "(.convInt " ++ reprParen ty ++ .text " " ++ reprPexpr e ++ .text ")")
    | .wrapI ty op e1 e2 =>
      .group (.text "(.wrapI " ++ reprParen ty ++ .text " " ++ repr op ++ .text " " ++ reprPexpr e1 ++ .text " " ++ reprPexpr e2 ++ .text ")")
    | .catchExceptionalCondition ty op e1 e2 =>
      .group (.text "(.catchExceptionalCondition " ++ reprParen ty ++ .text " " ++ repr op ++ .text " " ++ reprPexpr e1 ++ .text " " ++ reprPexpr e2 ++ .text ")")
    | .bmcAssume e => .group (.text "(.bmcAssume " ++ reprPexpr e ++ .text ")")
    | .pureMemop op args => .group (.text "(.pureMemop " ++ repr op ++ .text " " ++ reprPexprList args ++ .text ")")
    | .constrained constraints =>
      .group (.text "(.constrained " ++
        reprList (constraints.map fun (s, e) => .group (.text "(" ++ repr s ++ .text ", " ++ reprPexpr e ++ .text ")")) ++ .text ")")

  partial def reprPexprList (es : List Pexpr) : Std.Format :=
    .text "[" ++ .group (.nest 2 (.join (es.map fun e => reprPexpr e ++ .text ", "))) ++ .text "]"

  partial def reprAPattern (p : APattern) : Std.Format :=
    .group (.text "{ annots := " ++ repr p.annots ++ .text ", pat := " ++ reprPattern p.pat ++ .text " }")

  partial def reprPattern : Pattern → Std.Format
    -- sym is Option Sym, needs parentheses around `some {...}` or `none`
    | .base sym ty => .group (.text "(.base " ++ reprParen sym ++ .text " " ++ reprParen ty ++ .text ")")
    | .ctor c args => .group (.text "(.ctor " ++ repr c ++ .text " " ++ reprList (args.map reprPattern) ++ .text ")")

  partial def reprValue : Value → Std.Format
    | .object v => .group (.text "(.object " ++ reprObjectValue v ++ .text ")")
    | .loaded v => .group (.text "(.loaded " ++ reprLoadedValue v ++ .text ")")
    | .unit => .text ".unit"
    | .true_ => .text ".true_"
    | .false_ => .text ".false_"
    | .ctype ty => .group (.text "(.ctype " ++ reprParen ty ++ .text ")")
    | .list ty vs => .group (.text "(.list " ++ reprParen ty ++ .text " " ++ reprList (vs.map reprValue) ++ .text ")")
    | .tuple vs => .group (.text "(.tuple " ++ reprList (vs.map reprValue) ++ .text ")")

  partial def reprObjectValue : ObjectValue → Std.Format
    | .integer v => .group (.text "(.integer " ++ repr v ++ .text ")")
    | .floating v => .group (.text "(.floating " ++ repr v ++ .text ")")
    | .pointer v => .group (.text "(.pointer " ++ repr v ++ .text ")")
    | .array elems => .group (.text "(.array " ++ reprList (elems.map reprLoadedValue) ++ .text ")")
    | .struct_ tag members =>
      .group (.text "(.struct_ " ++ repr tag ++ .text " " ++
        reprList (members.map fun m => .group (.text "{ name := " ++ repr m.name ++ .text ", ty := " ++ repr m.ty ++ .text ", value := " ++ reprMemValue m.value ++ .text " }")) ++ .text ")")
    | .union_ tag member value =>
      .group (.text "(.union_ " ++ repr tag ++ .text " " ++ repr member ++ .text " " ++ reprMemValue value ++ .text ")")

  partial def reprLoadedValue : LoadedValue → Std.Format
    | .specified v => .group (.text "(.specified " ++ reprObjectValue v ++ .text ")")
    | .unspecified ty => .group (.text "(.unspecified " ++ reprParen ty ++ .text ")")

  partial def reprMemValue : MemValue → Std.Format
    | .unspecified ty => .group (.text "(.unspecified " ++ reprParen ty ++ .text ")")
    | .integer ity v => .group (.text "(.integer " ++ reprParen ity ++ .text " " ++ repr v ++ .text ")")
    | .floating fty v => .group (.text "(.floating " ++ reprParen fty ++ .text " " ++ repr v ++ .text ")")
    | .pointer ty v => .group (.text "(.pointer " ++ reprParen ty ++ .text " " ++ repr v ++ .text ")")
    | .array elems => .group (.text "(.array " ++ reprList (elems.map reprMemValue) ++ .text ")")
    | .struct_ tag members =>
      .group (.text "(.struct_ " ++ repr tag ++ .text " " ++
        reprList (members.map fun (id, ty, v) => .group (.text "(" ++ repr id ++ .text ", " ++ reprParen ty ++ .text ", " ++ reprMemValue v ++ .text ")")) ++ .text ")")
    | .union_ tag member value =>
      .group (.text "(.union_ " ++ repr tag ++ .text " " ++ repr member ++ .text " " ++ reprMemValue value ++ .text ")")

  partial def reprPaction (p : Paction) : Std.Format :=
    .group (.text "{ polarity := " ++ repr p.polarity ++ .text ", action := " ++ reprAAction p.action ++ .text " }")

  partial def reprAAction (a : AAction) : Std.Format :=
    .group (.text "{ loc := " ++ repr a.loc ++ .text ", action := " ++ reprAction a.action ++ .text " }")

  partial def reprAction : Action → Std.Format
    | .create align size prefix_ =>
      .group (.text ".create " ++ reprAPexpr align ++ .text " " ++ reprAPexpr size ++ .text " " ++ repr prefix_)
    | .createReadonly align size init prefix_ =>
      .group (.text ".createReadonly " ++ reprAPexpr align ++ .text " " ++ reprAPexpr size ++ .text " " ++ reprAPexpr init ++ .text " " ++ repr prefix_)
    | .alloc align size prefix_ =>
      .group (.text ".alloc " ++ reprAPexpr align ++ .text " " ++ reprAPexpr size ++ .text " " ++ repr prefix_)
    | .kill kind ptr =>
      .group (.text ".kill " ++ repr kind ++ .text " " ++ reprAPexpr ptr)
    | .store locking ty ptr val order =>
      .group (.text ".store " ++ repr locking ++ .text " " ++ reprAPexpr ty ++ .text " " ++ reprAPexpr ptr ++ .text " " ++ reprAPexpr val ++ .text " " ++ repr order)
    | .load ty ptr order =>
      .group (.text ".load " ++ reprAPexpr ty ++ .text " " ++ reprAPexpr ptr ++ .text " " ++ repr order)
    | .rmw ty ptr expected desired successOrd failOrd =>
      .group (.text ".rmw " ++ reprAPexpr ty ++ .text " " ++ reprAPexpr ptr ++ .text " " ++ reprAPexpr expected ++ .text " " ++ reprAPexpr desired ++ .text " " ++ repr successOrd ++ .text " " ++ repr failOrd)
    | .fence order => .group (.text ".fence " ++ repr order)
    | .compareExchangeStrong ty ptr expected desired successOrd failOrd =>
      .group (.text ".compareExchangeStrong " ++ reprAPexpr ty ++ .text " " ++ reprAPexpr ptr ++ .text " " ++ reprAPexpr expected ++ .text " " ++ reprAPexpr desired ++ .text " " ++ repr successOrd ++ .text " " ++ repr failOrd)
    | .compareExchangeWeak ty ptr expected desired successOrd failOrd =>
      .group (.text ".compareExchangeWeak " ++ reprAPexpr ty ++ .text " " ++ reprAPexpr ptr ++ .text " " ++ reprAPexpr expected ++ .text " " ++ reprAPexpr desired ++ .text " " ++ repr successOrd ++ .text " " ++ repr failOrd)
    | .seqRmw isUpdate ty ptr sym val =>
      .group (.text ".seqRmw " ++ repr isUpdate ++ .text " " ++ reprAPexpr ty ++ .text " " ++ reprAPexpr ptr ++ .text " " ++ repr sym ++ .text " " ++ reprAPexpr val)
end

-- Repr instances
instance : Repr Expr where
  reprPrec e _ := reprExpr e

instance : Repr AExpr where
  reprPrec e _ := reprAExpr e

instance : Repr Pexpr where
  reprPrec e _ := reprPexpr e

instance : Repr APexpr where
  reprPrec e _ := reprAPexpr e

instance : Repr Pattern where
  reprPrec p _ := reprPattern p

instance : Repr APattern where
  reprPrec p _ := reprAPattern p

instance : Repr Value where
  reprPrec v _ := reprValue v

instance : Repr ObjectValue where
  reprPrec v _ := reprObjectValue v

instance : Repr LoadedValue where
  reprPrec v _ := reprLoadedValue v

instance : Repr Action where
  reprPrec a _ := reprAction a

instance : Repr AAction where
  reprPrec a _ := reprAAction a

instance : Repr Paction where
  reprPrec p _ := reprPaction p

-- FunDecl repr
-- Note: Types with argument-taking constructors need parentheses to avoid parsing issues
def reprFunDecl : FunDecl → Std.Format
  | .fun_ retTy params body =>
    .group (.text ".fun_ " ++ reprParen retTy ++ .text " " ++ repr params ++ .text " " ++ reprAPexpr body)
  | .proc loc markerEnv retTy params body =>
    .group (.text ".proc " ++ reprParen loc ++ .text " " ++ reprParen markerEnv ++ .text " " ++ reprParen retTy ++ .text " " ++ repr params ++ .text " " ++ reprAExpr body)
  | .procDecl loc retTy paramTys =>
    .group (.text ".procDecl " ++ reprParen loc ++ .text " " ++ reprParen retTy ++ .text " " ++ repr paramTys)
  | .builtinDecl loc retTy paramTys =>
    .group (.text ".builtinDecl " ++ reprParen loc ++ .text " " ++ reprParen retTy ++ .text " " ++ repr paramTys)

instance : Repr FunDecl where
  reprPrec d _ := reprFunDecl d

-- ImplDecl repr
def reprImplDecl : ImplDecl → Std.Format
  | .def_ ty value => .group (.text ".def_ " ++ reprParen ty ++ .text " " ++ reprAPexpr value)
  | .ifun ty params body =>
    .group (.text ".ifun " ++ reprParen ty ++ .text " " ++ repr params ++ .text " " ++ reprAPexpr body)

instance : Repr ImplDecl where
  reprPrec d _ := reprImplDecl d

-- GlobDecl repr
def reprGlobDecl : GlobDecl → Std.Format
  | .def_ coreTy cTy init =>
    .group (.text ".def_ " ++ reprParen coreTy ++ .text " " ++ reprParen cTy ++ .text " " ++ reprAExpr init)
  | .decl coreTy cTy =>
    .group (.text ".decl " ++ reprParen coreTy ++ .text " " ++ reprParen cTy)

instance : Repr GlobDecl where
  reprPrec d _ := reprGlobDecl d

-- File repr (the main one we need)
-- Uses Format.line for soft breaks - becomes space if fits, newline if doesn't
def reprFile (f : File) : Std.Format :=
  .group (
    .text "{" ++
    .nest 2 (
      .line ++ .text "main := " ++ repr f.main ++ .text "," ++
      .line ++ .text "tagDefs := " ++ repr f.tagDefs ++ .text "," ++
      .line ++ .text "stdlib := " ++ reprFunMap f.stdlib ++ .text "," ++
      .line ++ .text "impl := " ++ reprImplDefs f.impl ++ .text "," ++
      .line ++ .text "globs := " ++ reprGlobs f.globs ++ .text "," ++
      .line ++ .text "funs := " ++ reprFunMap f.funs ++ .text "," ++
      .line ++ .text "extern := " ++ reprExtern f.extern ++ .text "," ++
      .line ++ .text "funinfo := " ++ reprFunInfo f.funinfo
    ) ++
    .line ++ .text "}"
  )
where
  reprFunMap (m : FunMap) : Std.Format :=
    .group (
      .text "[" ++
      .nest 2 (.join (m.map fun (s, d) =>
        .line ++ .group (.text "(" ++ repr s ++ .text ", " ++ reprFunDecl d ++ .text "),"))) ++
      .line ++ .text "]"
    )
  reprImplDefs (m : ImplDefs) : Std.Format :=
    let items := m.toList
    .group (
      .text "Std.HashMap.ofList [" ++
      .nest 2 (.join (items.map fun (c, d) =>
        .line ++ .group (.text "(" ++ repr c ++ .text ", " ++ reprImplDecl d ++ .text "),"))) ++
      .line ++ .text "]"
    )
  reprGlobs (g : List (Sym × GlobDecl)) : Std.Format :=
    .group (
      .text "[" ++
      .nest 2 (.join (g.map fun (s, d) =>
        .line ++ .group (.text "(" ++ repr s ++ .text ", " ++ reprGlobDecl d ++ .text "),"))) ++
      .line ++ .text "]"
    )
  reprExtern (e : Std.HashMap Identifier (List Sym × LinkingKind)) : Std.Format :=
    let items := e.toList
    .group (
      .text "Std.HashMap.ofList [" ++
      .nest 2 (.join (items.map fun (id, (syms, lk)) =>
        .line ++ .group (.text "(" ++ repr id ++ .text ", (" ++ repr syms ++ .text ", " ++ repr lk ++ .text ")),"))) ++
      .line ++ .text "]"
    )
  reprFunInfo (m : FunInfoMap) : Std.Format :=
    let items := m.toList
    .group (
      .text "Std.HashMap.ofList [" ++
      .nest 2 (.join (items.map fun (s, info) =>
        .line ++ .group (.text "(" ++ repr s ++ .text ", " ++ repr info ++ .text "),"))) ++
      .line ++ .text "]"
    )

instance : Repr File where
  reprPrec f _ := reprFile f

end CerbLean.Core
