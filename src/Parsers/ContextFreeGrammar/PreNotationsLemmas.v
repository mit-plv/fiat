Require Import Coq.Strings.String.
Require Import Fiat.Parsers.GenericBaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.

Section with_actions.
  Context {Char T : Type}
          (G : pregrammar_with_actions Char T).

  Definition option_cons {A}
    : option A -> option (list A) -> option (list A)
    := fun pit pits
       => match pit, pits with
          | Some pit', Some pits' => Some (cons pit' pits')
          | None, _ => None
          | _, None => None
          end.

  Definition option_orb {A} (x y : option A) : option A
    := match x, y with
       | Some x', _ => Some x'
       | None, Some y' => Some y'
       | None, None => None
       end.

  Fixpoint fuse_production (res : list (Char + T)) (pat : rproduction_with_action Char T) : option T
    := match res, projT1 pat as pat' return action_of_rproduction T pat' -> option T with
       | nil, nil => @Some _
       | inl v :: res', Reflective.RTerminal _ :: pats'
       | inr v :: res', Reflective.RNonTerminal _ :: pats'
         => fun f => @fuse_production res' (existT _ pats' (f v))
       | inl _ :: _, Reflective.RNonTerminal _ :: _
       | inr _ :: _, Reflective.RTerminal _ :: _
       | nil, _::_ | _::_, nil => fun _ => None
       end%list (projT2 pat).

  Fixpoint fuse_productions (res : list (option (list (Char + T)))) (pats : rproductions_with_actions Char T) : option T
    := match res, pats with
       | nil, nil => None
       | Some pact :: res', pat :: pats'
         => match fuse_production pact pat with
            | Some t => Some t
            | None => fuse_productions res' pats'
            end
       | None :: res', pat :: pats'
         => fuse_productions res' pats'
       | _::_, nil | nil, _::_ => None
       end%list.

  Global Instance generic_parser_data_from_actions : generic_parser_dataT Char
    := { parse_nt_T := option T;
         parse_item_T := option (Char + T);
         parse_production_T := option (list (Char + T));
         parse_productions_T := list (option (list (Char + T)));
         ret_Terminal_false ch := None;
         ret_Terminal_true ch := Some (inl ch);
         ret_NonTerminal_false nt := None;
         ret_NonTerminal_true nt v := option_map (@inr _ _) v;
         ret_production_cons := option_cons;
         ret_orb_production := option_orb;
         ret_orb_production_base := None;
         ret_production_nil_true := Some nil;
         ret_production_nil_false := None;
         ret_orb_productions := cons;
         ret_orb_productions_base := nil;
         ret_nt nt v := fuse_productions v (List.nth (default_of_nonterminal (G:=G) nt) (List.map snd (pregrammar_arproductions G)) nil);
         ret_nt_invalid := None }.
End with_actions.
