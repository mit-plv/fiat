Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Fiat.Parsers.Reflective.Syntax.
Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope string_scope.

Section syntactify.
  Context (var : TypeCode -> Type).

  Definition syntactify_list {T : SimpleTypeCode} (ls : list (Term var T)) : Term var (clist T)
    := list_rect
         (fun _ => Term _ _)
         (RLiteralApp Rnil noargs)
         (fun x _ xs
          => RLiteralApp Rcons (x :: xs :: noargs))
         ls.

  Definition syntactify_prod {A B : SimpleTypeCode} (xy : Term var A * Term var B) : Term var (A * B)
    := RLiteralApp Rpair (fst xy :: snd xy :: noargs).

  Definition syntactify_nat (n : nat) : Term var cnat
    := nat_rect
         (fun _ => Term _ _)
         (RLiteralApp RO noargs)
         (fun _ n'
          => RLiteralApp RS (n' :: noargs))
         n.

  Definition syntactify_bool (v : bool) : Term var cbool
    := RLiteralApp (Rbool v) noargs.
  Definition syntactify_rchar_expr_ascii (v : Reflective.RCharExpr ascii)
    : Term var crchar_expr_ascii
    := RLiteralApp (Rrchar_expr_ascii v) noargs.
  Definition syntactify_ritem_ascii (v : Reflective.ritem ascii)
    : Term var critem_ascii
    := RLiteralApp (Rritem_ascii v) noargs.
  Definition syntactify_string (v : string)
    : Term var cstring
    := RLiteralApp (Rstring v) noargs.
  Definition syntactify_rproductions
             (Gp : list (string * Reflective.rproductions ascii))
    : Term var _
    := syntactify_list
         (List.map
            (fun xy
             => syntactify_prod
                  (syntactify_string (fst xy),
                   syntactify_list
                     (List.map
                        (fun ls
                         => syntactify_list
                              (List.map
                                 syntactify_ritem_ascii
                                 ls))
                        (snd xy))))
            Gp).
End syntactify.
