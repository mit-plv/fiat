Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.XmlLang.
Export XmlOutput XmlLang.


Coercion XmlLang.Cdata : string >-> XmlLang.pat.
Notation "$ x" := (XmlLang.Var x) (at level 0) : pat_scope.
Notation "$$ x" := (XmlLang.TreeVar x) (at level 0) : pat_scope.
Infix "/" := XmlLang.Tag : pat_scope.
Infix "&" := XmlLang.Both (at level 41, right associativity) : pat_scope.
Infix ";;" := XmlLang.Ordered : pat_scope.
Delimit Scope pat_scope with pat.
Bind Scope pat_scope with pat.

Coercion Const : string >-> exp.
Notation "$ x" := (Input x) : exp_scope.
Delimit Scope exp_scope with exp.
Bind Scope exp_scope with exp.

Notation "col = e" := ((col, e%exp) :: nil) : condition_scope.
Infix "&&" := app : condition_scope.
Delimit Scope condition_scope with condition.

Coercion XCdata : string >-> xml.
Notation "$ x" := (XVar x) : out_scope.
Notation "tab # col" := (XColumn tab col) (at level 0) : out_scope.
Definition xcons (x : xml) (xs : list xml) : list xml := x :: xs.
Notation "<*> tag </> x1 , .. , xN </>" := (XTag tag (xcons x1 .. (xcons xN nil) ..))
  (tag at level 0) : out_scope.
Delimit Scope out_scope with out.
Notation "'From' tab 'Where' cond 'Write' o" :=
  (XSelect tab cond%condition o%out)
  (at level 0, tab at level 0, cond at level 0, o at level 0) : out_scope.
Notation "'From' tab 'Write' o" :=
  (XSelect tab nil o%out)
  (at level 0, tab at level 0, o at level 0) : out_scope.
Definition forJoin (o : xml) :=
  match o with
    | XColumn tab col => (tab, col)
    | _ => ("", "")
  end.
Notation "'Join' x1 'to' x2 ;;; o" :=
  (let (tab1, col1) := forJoin x1 in
    let (tab2, col2) := forJoin x2 in
      XIfEqual tab1 col1 tab2 col2 o%out)
  (at level 95, o at level 0) : out_scope.
Bind Scope out_scope with xml.

Definition econs (x : exp) (xs : list exp) : list exp := x :: xs.
Notation "'Insert' t ( e1 , .. , eN )" := (XmlLang.Insert t (econs e1%exp .. (econs eN%exp nil) ..))
  (at level 0, t at level 0) : action_scope.
Notation "'Delete' tab 'Where' cond" :=
  (Delete tab cond%condition)
  (at level 0, tab at level 0, cond at level 0) : action_scope.
Notation "'Write' o" := (Output o%out) (at level 0, o at level 0) : action_scope.
Infix ";;" := Seq : action_scope.
Notation "'IfHas' tab 'Where' cond 'then' a1 'else' a2 'end'" :=
  (IfExists tab cond%condition a1 a2)
  (at level 0, tab at level 0, cond at level 0, a1 at level 0, a2 at level 0) : action_scope.
Delimit Scope action_scope with action.
Notation "'From' tab 'Where' cond 'Do' a" :=
  (XmlLang.Select tab cond%condition a%action)
  (at level 0, tab at level 0, cond at level 0, a at level 0) : action_scope.
Notation "'From' tab 'Do' a" :=
  (XmlLang.Select tab nil a%action)
  (at level 0, tab at level 0, a at level 0) : action_scope.
Notation "'Send' x1 'Value' x2" :=
  (XmlLang.SendTo x1%out x2%out) (at level 0, x1 at level 0, x2 at level 0) : action_scope.
Bind Scope action_scope with action.

Notation "'Match' p 'Do' a 'end'" := (Rule p%pat a%action) : program_scope.
Infix ";;" := PSeq : program_scope.
Delimit Scope program_scope with program.
Bind Scope program_scope with program.

Ltac wf'' :=
  match goal with
    | [ |- exists t, _ /\ Name t = ?s /\ _ ] =>
      match goal with
        | [ |- context[{| Name := s; Address := ?a; Schema := ?sch |}] ] =>
          exists {| Name := s; Address := a; Schema := sch |}; simpl; intuition
      end
    | _ =>
      repeat match goal with
               | [ H : List.Exists _ _ |- _ ] => inversion H; clear H; subst
             end; simpl in *; tauto
    | _ => constructor
  end.

Ltac wf' :=
  match goal with
    | [ |- (_ <= _)%nat ] => compute; omega
    | [ |- (_ >= _)%N ] => discriminate
    | [ |- (_ < _)%N ] => reflexivity
    | [ |- NoDup _ ] => NoDup
    | [ |- twfs _ ] => repeat constructor
    | [ |- uf _ ] => repeat (constructor; simpl; intuition (try congruence))
    | _ => simpl; intuition (try (congruence || reflexivity || NoDup)); repeat wf''
  end.

Ltac wf := constructor; wf'.
