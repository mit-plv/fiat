Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Wrap Bedrock.Platform.StringOps Bedrock.Platform.SinglyLinkedList Bedrock.Platform.Malloc Bedrock.Platform.ArrayOps Bedrock.Platform.Bags.
Require Import Bedrock.Platform.RelDb Bedrock.Platform.RelDbCondition Bedrock.Platform.RelDbSelect.


Set Implicit Arguments.


(** * A language for generating XML code *)

Inductive xml :=
| Cdata (const : string)
| Var (start len : string)
| Tag (tag : string) (inner : list xml)
| Column (tab : string) (col : string)
| Select (tab rw data : string) (cond : condition) (inner : xml)
| IfEqual (tab1 col1 tab2 col2 : string) (inner : xml).

Section ForallR.
  Variable A : Type.
  Variable P : A -> Prop.

  Fixpoint ForallR (ls : list A) : Prop :=
    match ls with
      | nil => True
      | x :: ls' => P x /\ ForallR ls'
    end.

  Theorem Forall_ForallR : forall ls, List.Forall P ls -> ForallR ls.
    induction 1; simpl; intuition.
  Qed.

  Theorem ForallR_Forall : forall ls, ForallR ls -> List.Forall P ls.
    induction ls; simpl; intuition.
  Qed.

  Fixpoint ExistsR (ls : list A) : Prop :=
    match ls with
      | nil => False
      | x :: ls' => P x \/ ExistsR ls'
    end.

  Theorem Exists_ExistsR : forall ls, List.Exists P ls -> ExistsR ls.
    induction 1; simpl; intuition.
  Qed.

  Theorem ExistsR_Exists : forall ls, ExistsR ls -> List.Exists P ls.
    induction ls; simpl; intuition.
  Qed.
End ForallR.

Record table := {
  Name : string;
  Address : W;
  Schema : schema
}.

Record avail := {
  Table : table;
  Row : string;
  Data : string
}.

Definition twf (t : table) := goodSize (2 + length (Schema t) + length (Schema t)).

Definition tables := list table.
Definition twfs : tables -> Prop := List.Forall twf.

Definition ewf (ns : list string) (cdatas : list (string * string)) (e : exp) : Prop :=
  match e with
    | Const s => goodSize (String.length s)
    | Input pos len => In pos ns /\ In len ns /\ ~ In pos baseVars /\ ~ In len baseVars
      /\ In (pos, len) cdatas
  end.

Definition eqwf ns (sch : schema) cdatas (e : equality) : Prop :=
  In (fst e) sch /\ ewf ns cdatas (snd e).

Definition cwf ns sch cdatas : condition -> Prop := List.Forall (eqwf ns sch cdatas).

Fixpoint removeTable (tab : string) (ts : tables) : tables :=
  match ts with
    | nil => nil
    | t :: ts => if string_dec tab (Name t) then removeTable tab ts else t :: removeTable tab ts
  end.

Definition cvars := "rp" :: "ibuf" :: "overflowed" :: "ipos" :: "ilen"
  :: "opos" :: "tmp" :: "len" :: "buf" :: "matched" :: "res" :: "obuf"
  :: "olen" :: nil.

Definition dontTouch rw data :=
  ForallR (fun p : string * string => fst p <> rw /\ snd p <> rw /\ fst p <> data /\ snd p <> data).

Definition dontReuse rw data :=
  ForallR (fun av => Row av <> rw /\ Row av <> data /\ Data av <> rw /\ Data av <> data).

Fixpoint wf ns (cdatas : list (string * string)) (avs : list avail) (ts : list table) (xm : xml) : Prop :=
  match xm with
    | Cdata const => goodSize (String.length const)
    | Var _ _ => True
    | Tag tag inner => goodSize (String.length tag + 3) /\ ForallR (wf ns cdatas avs ts) inner
    | Column tab col => exists av, In av avs /\ Name (Table av) = tab /\ In col (Schema (Table av))
      /\ In (Data av) ns
    | Select tab rw data cond inner =>
      rw <> data /\ ~In rw cvars /\ ~In data cvars
      /\ dontTouch rw data cdatas /\ dontReuse rw data avs
      /\ exists t, In t ts /\ Name t = tab /\ cwf ns (Schema t) cdatas cond
        /\ wf ns cdatas ({| Table := t; Row := rw; Data := data |} :: avs)
        (removeTable tab ts) inner
    | IfEqual tab1 col1 tab2 col2 inner => tab1 <> tab2
      /\ (exists av, In av avs /\ Name (Table av) = tab1
        /\ In col1 (Schema (Table av))
        /\ In (Data av) ns)
      /\ (exists av, In av avs /\ Name (Table av) = tab2
        /\ In col2 (Schema (Table av))
        /\ In (Data av) ns)
      /\ wf ns cdatas avs ts inner
  end.


Definition efreeVar (e : exp) (xs : string * string) : Prop :=
  match e with
    | Const _ => False
    | Input pos len => xs = (pos, len)
  end.

Fixpoint freeVar (xm : xml) (xs : string * string) : Prop :=
  match xm with
    | Cdata _ => False
    | Var start len => xs = (start, len)
    | Tag _ inner => ExistsR (fun xm' => freeVar xm' xs) inner
    | Column _ _ => False
    | Select _ _ _ cond inner => List.Exists (fun e => efreeVar (snd e) xs) cond
      \/ freeVar inner xs
    | IfEqual _ _ _ _ inner => freeVar inner xs
  end.

Fixpoint bindsRowVar (xm : xml) (xs : string * string) : Prop :=
  match xm with
    | Cdata _ => False
    | Var _ _ => False
    | Tag _ inner => ExistsR (fun xm' => bindsRowVar xm' xs) inner
    | Column _ _ => False
    | Select _ rw data _ inner => xs = (rw, data) \/ bindsRowVar inner xs
    | IfEqual _ _ _ _ inner => bindsRowVar inner xs
  end.

Section xml_ind'.
  Variable P : xml -> Prop.

  Hypothesis H_Cdata : forall const, P (Cdata const).

  Hypothesis H_Var : forall start len, P (Var start len).

  Hypothesis H_Tag : forall tag inner, List.Forall P inner -> P (Tag tag inner).

  Hypothesis H_Column : forall tab col, P (Column tab col).

  Hypothesis H_Select : forall tab rw data cond inner, P inner
    -> P (Select tab rw data cond inner).

  Hypothesis H_IfEqual : forall tab1 col1 tab2 col2 inner, P inner
    -> P (IfEqual tab1 col1 tab2 col2 inner).

  Fixpoint xml_ind' (xm : xml) : P xm :=
    match xm with
      | Cdata const => H_Cdata const
      | Var start len => H_Var start len
      | Tag tag inner => H_Tag tag ((fix xmls_ind (xms : list xml) : List.Forall P xms :=
        match xms with
          | nil => Forall_nil _
          | xm :: xms' => Forall_cons _ (xml_ind' xm) (xmls_ind xms')
        end) inner)
      | Column tab col => H_Column tab col
      | Select tab rw data cond inner =>
        H_Select tab rw data cond (xml_ind' inner)
      | IfEqual tab1 col1 tab2 col2 inner =>
        H_IfEqual tab1 col1 tab2 col2 (xml_ind' inner)
    end.
End xml_ind'.

Opaque xml_ind'.

Definition inBounds (cdatas : list (string * string)) (V : vals) :=
  List.Forall (fun p => wordToNat (V (fst p)) + wordToNat (V (snd p)) <= wordToNat (V "len"))%nat
  cdatas.

Definition db := starL (fun t => RelDb.table (Schema t) (Address t)).
Definition cursor (V : vals) (av : avail) := (
  row (Schema (Table av)) (V (Data av))
  * RelDbSelect.inv (Address (Table av)) (Schema (Table av)) (V (Row av)) (V (Data av))
)%Sep.
Definition cursors (V : vals) := starL (cursor V).

Fixpoint findTable (tab : string) (ts : tables) : option table :=
  match ts with
    | nil => None
    | t :: ts => if string_dec tab (Name t) then Some t else findTable tab ts
  end.

Fixpoint findCursor (tab : string) (avs : list avail) : option avail :=
  match avs with
    | nil => None
    | av :: avs => if string_dec tab (Name (Table av)) then Some av else findCursor tab avs
  end.

Fixpoint findCol (sch : schema) (s : string) : nat :=
  match sch with
    | nil => O
    | s' :: sch' => if string_dec s s' then O else S (findCol sch' s)
  end.

Fixpoint removeCursor (tab : string) (avs : list avail) : list avail :=
  match avs with
    | nil => nil
    | av :: avs => if string_dec tab (Name (Table av)) then removeCursor tab avs
      else av :: removeCursor tab avs
  end.

Ltac ift := match goal with
              | [ |- context[if ?E then _ else _] ] => destruct E; intuition
            end.

Definition Names := map Name.

Lemma findTable_good : forall tab t ts0,
  NoDup (Names ts0)
  -> In t ts0
  -> Name t = tab
  -> findTable tab ts0 = Some t.
  induction ts0; simpl; inversion 1; intuition subst; ift.
  exfalso; eapply H2.
  rewrite <- e.
  apply in_map; auto.
Qed.

Lemma removeTable_irrel_fwd : forall x ts,
  ~In x (Names ts)
  -> db ts ===> db (removeTable x ts).
  induction ts; simpl; intuition subst; try ift; sepLemma.
Qed.

Lemma removeTable_irrel_bwd : forall x ts,
  ~In x (Names ts)
  -> db (removeTable x ts) ===> db ts.
  induction ts; simpl; intuition subst; try ift; sepLemma.
Qed.

Hint Immediate removeTable_irrel_fwd removeTable_irrel_bwd.

Lemma removeTable_bwd : forall x ts,
  NoDup (Names ts)
  -> In x ts
  -> RelDb.table (Schema x) (Address x) * db (removeTable (Name x) ts)
  ===> db ts.
  induction ts; inversion 1; simpl; intuition subst;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E; intuition
    end.
  apply Himp_star_frame; try apply Himp_refl; auto.
  exfalso; apply H2; rewrite <- e; eapply in_map; auto.
  simpl.

  sepLemma.
  etransitivity; [ | apply H6 ]; sepLemma.
Qed.

Lemma removeTable_fwd : forall x ts,
  NoDup (Names ts)
  -> In x ts
  -> db ts ===> RelDb.table (Schema x) (Address x) * db (removeTable (Name x) ts).
  induction ts; inversion 1; simpl; intuition subst;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E; intuition
    end.
  apply Himp_star_frame; try apply Himp_refl; auto.
  exfalso; apply H2; rewrite <- e; eapply in_map; auto.
  simpl.

  sepLemma.
  etransitivity; [ apply H6 | ]; sepLemma.
Qed.

Lemma mult4_S : forall n, 4 * S n = S (S (S (S (4 * n)))).
  simpl; intros; omega.
Qed.

Definition cdatasGood (cdatas : list (string * string)) :=
  List.Forall (fun p => fst p <> "opos" /\ fst p <> "overflowed" /\ fst p <> "tmp" /\ fst p <> "matched"
    /\ fst p <> "res" /\ fst p <> "ibuf" /\ fst p <> "ilen" /\ fst p <> "ipos"
    /\ snd p <> "opos" /\ snd p <> "overflowed" /\ snd p <> "tmp" /\ snd p <> "matched"
    /\ snd p <> "res" /\ snd p <> "ibuf" /\ snd p <> "ilen" /\ snd p <> "ipos")
  cdatas.

Lemma removeTable_bwd' : forall x ts P,
  NoDup (Names ts)
  -> In x ts
  -> RelDb.table (Schema x) (Address x) * (db (removeTable (Name x) ts) * P)
  ===> P * db ts.
  intros; eapply Himp_trans; [ apply Himp_star_assoc' | ].
  eapply Himp_trans; [ | apply Himp_star_comm ].
  apply Himp_star_frame; try apply Himp_refl.
  apply removeTable_bwd; auto.
Qed.

Lemma removeTable_fwd' : forall x ts P,
  NoDup (Names ts)
  -> In x ts
  -> P * db ts
  ===> RelDb.table (Schema x) (Address x) * (P * db (removeTable (Name x) ts)).
  intros; eapply Himp_trans; [ | apply Himp_star_frame; [ | apply Himp_star_comm ] ].
  intros; eapply Himp_trans; [ | apply Himp_star_assoc ].
  eapply Himp_trans; [ apply Himp_star_comm | ].
  apply Himp_star_frame; try apply Himp_refl.
  apply removeTable_fwd; auto.
  apply Himp_refl.
Qed.

Lemma make_cursor : forall specs t V rw data P,
  himp specs (row (Schema t) (sel V data)
    * (inv (Address t) (Schema t) (sel V rw) (sel V data) * P))%Sep
  (P * cursor V {| Table := t; Row := rw; Data := data |})%Sep.
sepLemma; apply himp_star_comm.
Qed.

Lemma unmake_cursor : forall specs t V rw data P,
  himp specs (P * cursor V {| Table := t; Row := rw; Data := data |})%Sep
  (row (Schema t) (sel V data)
    * (inv (Address t) (Schema t) (sel V rw) (sel V data) * P))%Sep.
sepLemma; apply himp_star_comm.
Qed.

Theorem matchup : forall P Q R P' Q',
  P ===> P'
  -> Q ===> Q'
  -> P * (Q * R) ===> R * (P' * Q').
  sepLemma; eapply Himp_star_frame; eauto.
Qed.

Theorem matchup2 : forall P Q R Q' R',
  Q ===> Q'
  -> R ===> R'
  -> P * (Q * R) ===> P * (Q' * R').
  sepLemma; eapply Himp_star_frame; eauto.
Qed.

Definition ANames := map (fun av => Name (Table av)).

Lemma cursors_irrel : forall V av avs,
  ~In (Name (Table av)) (ANames avs)
  -> cursors V (removeCursor (Name (Table av)) avs) ===> cursors V avs.
  induction avs; simpl; intuition; try ift; sepLemma.
Qed.

Theorem grab_cursor : forall V av avs,
  In av avs
  -> NoDup (ANames avs)
  -> (cursors V (removeCursor (Name (Table av)) avs)
    * inv (Address (Table av)) (Schema (Table av))
    (sel V (Row av)) (sel V (Data av))
    * row (Schema (Table av)) (sel V (Data av)))
  ===> cursors V avs.
  clear; induction avs; inversion_clear 2; simpl in *; intuition subst.
  ift.
  unfold cursor.
  repeat match goal with
           | [ |- context[V ?x] ] => change (V x) with (sel V x)
         end.
  sepLemma.
  apply cursors_irrel; auto.
  ift.
  exfalso; apply H1.
  rewrite <- e.
  apply (in_map (fun av => Name (Table av))); auto.
  simpl.
  sepLemma.
  etransitivity; [ | apply H3 ].
  sepLemma.
Qed.

Lemma cursors_irrel' : forall V av avs,
  ~In (Name (Table av)) (ANames avs)
  -> cursors V avs ===> cursors V (removeCursor (Name (Table av)) avs).
  induction avs; simpl; intuition; try ift; sepLemma.
Qed.

Theorem release_cursor : forall V av avs,
  In av avs
  -> NoDup (ANames avs)
  -> cursors V avs
  ===> cursor V av * cursors V (removeCursor (Name (Table av)) avs).
  clear; induction avs; inversion_clear 2; simpl in *; intuition subst; ift.
  sepLemma.
  apply cursors_irrel'; auto.
  exfalso; apply H1.
  rewrite <- e.
  apply (in_map (fun av => Name (Table av))); auto.
  sepLemma.
  etransitivity; [ | apply himp_star_comm ]; auto.
Qed.

Definition goodCursors avs := List.Forall (fun av => ~In (Row av) cvars /\ ~In (Data av) cvars
  /\ goodSize (length (Schema (Table av)))) avs.

Lemma weaken_cursors : forall specs V V',
  (forall x, x <> "overflowed" -> x <> "opos"
    -> x <> "tmp" -> x <> "matched" -> x <> "res"
    -> sel V x = sel V' x)
  -> forall avs,
    goodCursors avs
    -> himp specs (cursors V avs) (cursors V' avs).
  induction avs; inversion_clear 1; simpl; intuition.
  apply himp_star_frame; auto.
  unfold cvars in *; simpl in *; intuition idtac;
    unfold cursor; apply himp_star_frame;
      repeat match goal with
               | [ V : vals |- _ ] =>
                 progress repeat match goal with
                                   | [ |- context[V ?x] ] => change (V x) with (sel V x)
                                 end
             end;
      try match goal with
            | [ H : forall x : string, _ |- _ ] => repeat rewrite H by congruence
          end; reflexivity.
Qed.

Hint Resolve weaken_cursors.

Lemma Weaken_cursors : forall V V',
  (forall x, x <> "overflowed" -> x <> "opos"
    -> x <> "tmp" -> x <> "matched" -> x <> "res" -> sel V x = sel V' x)
  -> forall avs,
    goodCursors avs
    -> cursors V avs ===> cursors V' avs.
  intros; hnf; intros; apply weaken_cursors; auto.
Qed.

Hint Extern 1 (cursors _ _ ===> cursors _ _) =>
  apply Weaken_cursors; eauto 1; [ descend ].

Lemma cursor_expand : forall V' V P Q avs av,
  In av avs
  -> NoDup (ANames avs)
  -> goodCursors avs
  -> (forall x, x <> "overflowed" -> x <> "opos" ->
    x <> "tmp" -> x <> "matched" -> x <> "res" -> sel V' x = sel V x)
  -> P * Q * cursors V' (removeCursor (Name (Table av)) avs)
  * inv (Address (Table av)) (Schema (Table av))
  (sel V' (Row av)) (sel V' (Data av))
  * row (Schema (Table av)) (sel V' (Data av)) ===> P * (Q * cursors V avs).
  sepLemma.
  etransitivity; [ | eapply weaken_cursors ]; try eassumption.
  etransitivity; [ | apply grab_cursor ]; eauto.
  sepLemma.
Qed.

Lemma cursor_expand' : forall V' V P Q avs av,
  In av avs
  -> NoDup (ANames avs)
  -> goodCursors avs
  -> (forall x, x <> "overflowed" -> x <> "opos" ->
    x <> "tmp" -> x <> "matched" -> x <> "res" -> sel V' x = sel V x)
  -> P * Q * cursors V' (removeCursor (Name (Table av)) avs)
  * inv (Address (Table av)) (Schema (Table av))
  (sel V' (Row av)) (sel V' (Data av))
  * row (Schema (Table av)) (sel V' (Data av)) ===> P * (cursors V avs * Q).
  sepLemma.
  etransitivity; [ | eapply weaken_cursors ]; try eassumption.
  etransitivity; [ | apply grab_cursor ]; eauto.
  sepLemma.
Qed.

Hint Constructors unit.

Lemma length_append : forall s1 s2, String.length (s1 ++ s2) = String.length s1 + String.length s2.
  induction s1; simpl; intuition.
Qed.

Hint Rewrite length_append : sepFormula.

Lemma Forall_impl2 : forall A (P Q R : A -> Prop) ls,
  List.Forall P ls
  -> List.Forall Q ls
  -> (forall x, P x -> Q x -> R x)
  -> List.Forall R ls.
  induction 1; inversion 1; eauto.
Qed.

Lemma wplus_wminus : forall u v : W, u ^+ v ^- v = u.
  intros; words.
Qed.

Hint Rewrite wplus_wminus mult4_S : sepFormula.

Lemma findCol_bound : forall s col,
  In col s
  -> (findCol s col < length s)%nat.
  clear; induction s; simpl; intuition subst;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E
    end; intuition.
Qed.

Lemma findCol_bound_natToW : forall sch col n,
  In col sch
  -> goodSize (Datatypes.length sch)
  -> n = length sch
  -> natToW (findCol sch col) < natToW n.
  clear; intros; subst.
  pre_nomega.
  rewrite wordToNat_natToWord_idempotent.
  rewrite wordToNat_natToWord_idempotent.
  eauto using findCol_bound.
  apply findCol_bound in H; congruence.
  change (goodSize (findCol sch col)); eapply goodSize_weaken; eauto.
  apply findCol_bound in H; auto.
Qed.

Lemma findCol_posl : forall sch col cols,
  In col sch
  -> goodSize (Datatypes.length sch)
  -> length cols = length sch
  -> natToW (findCol sch col) < natToW (length (posl cols)).
  intros; rewrite length_posl; eauto using findCol_bound_natToW.
Qed.

Lemma findCol_lenl : forall sch col cols,
  In col sch
  -> goodSize (Datatypes.length sch)
  -> length cols = length sch
  -> natToW (findCol sch col) < natToW (length (lenl cols)).
  intros; rewrite length_lenl; eauto using findCol_bound_natToW.
Qed.

Hint Resolve findCol_posl findCol_lenl.

Lemma selN_col : forall sch col cols,
  In col sch
  -> goodSize (length sch)
  -> length cols = length sch
  -> Array.sel cols (natToW (findCol sch col)) = selN cols (findCol sch col).
  clear; unfold Array.sel; intros; f_equal.
  apply wordToNat_natToWord_idempotent.
  change (goodSize (findCol sch col)).
  eapply goodSize_weaken; eauto.
  apply findCol_bound in H; auto.
Qed.

Lemma selN_posl : forall sch col cols,
  In col sch
  -> goodSize (length sch)
  -> length cols = length sch
  -> Array.sel (posl cols) (natToW (findCol sch col)) = selN (posl cols) (findCol sch col).
  intros; apply selN_col; auto; rewrite length_posl; auto.
Qed.

Lemma selN_lenl : forall sch col cols,
  In col sch
  -> goodSize (length sch)
  -> length cols = length sch
  -> Array.sel (lenl cols) (natToW (findCol sch col)) = selN (lenl cols) (findCol sch col).
  intros; apply selN_col; auto; rewrite length_lenl; auto.
Qed.

Hint Resolve selN_posl selN_lenl.

Lemma inBounds_selN : forall sch len cols,
  RelDb.inBounds len cols
  -> forall col a b c, a = selN (posl cols) (findCol sch col)
    -> b = selN (lenl cols) (findCol sch col)
    -> c = wordToNat len
    -> In col sch
    -> length cols = length sch
    -> (wordToNat a + wordToNat b <= c)%nat.
  intros; eapply inBounds_selN; try eassumption.
  rewrite H4; eapply findCol_bound; auto.
Qed.

Hint Resolve inBounds_selN.

Hint Extern 1 (_ + _ <= _)%nat =>
  eapply inBounds_selN; try eassumption; (cbv beta; congruence).

Lemma findCursor_good : forall tab av avs,
  NoDup (map (fun av => Name (Table av)) avs)
  -> Name (Table av) = tab
  -> In av avs
  -> findCursor tab avs = Some av.
  induction avs; simpl; inversion 1; intuition subst; ift.
  exfalso; eapply H2.
  rewrite <- e.
  eapply (in_map (fun av => Name (Table av)) _ _ H6).
Qed.

Lemma inBounds_inputOk : forall ns sch V cdatas,
  inBounds cdatas V
  -> forall cond, cwf ns sch cdatas cond
    -> inputOk V (exps cond).
  clear; induction 2; simpl; constructor; auto.
  unfold eqwf in *; destruct x; simpl in *; intuition.
  destruct e; simpl in *; intuition idtac.
  eapply Forall_forall in H; [ | eauto ]; eauto.
Qed.

Hint Immediate inBounds_inputOk.

Lemma inBounds_weaken_dontTouch : forall cdatas V rw data V',
  inBounds cdatas V
  -> dontTouch rw data cdatas
  -> cdatasGood cdatas
  -> ~In rw cvars
  -> ~In data cvars
  -> (forall x, x <> rw -> x <> data
    -> x <> "ibuf" -> x <> "ilen" -> x <> "tmp" -> x <> "ipos"
    -> x <> "overflowed" -> x <> "matched" -> sel V x = sel V' x)
  -> inBounds cdatas V'.
  clear; intros; eapply Forall_impl3; [ apply H | apply ForallR_Forall; apply H0 | apply H1 | ].
  simpl in *; intuition idtac.
  match goal with
    | [ H : (_ <= _)%nat |- _ ] => generalize dependent H;
      repeat match goal with
               | [ V : vals |- _ ] =>
                 progress repeat match goal with
                                   | [ |- context[V ?x] ] => change (V x) with (sel V x)
                                 end
             end; intros
  end.
  repeat rewrite <- H4 by congruence.
  assumption.
Qed.

Hint Extern 1 (inBounds _ _) => eapply inBounds_weaken_dontTouch; try eassumption;
  [ | ]; (simpl; tauto).

Hint Extern 1 False =>
  match goal with
    | [ H : forall rw data : string, _ \/ _ -> _ |- _ ] =>
      specialize (H _ _ (or_introl _ eq_refl)); tauto
  end.

Lemma weaken_cursors' : forall rw data specs V V',
  (forall x, x <> rw -> x <> data
    -> x <> "ibuf" -> x <> "ilen" -> x <> "tmp" -> x <> "ipos"
    -> x <> "overflowed" -> x <> "matched" -> sel V x = sel V' x)
  -> forall avs,
    goodCursors avs
    -> dontReuse rw data avs
    -> himp specs (cursors V avs) (cursors V' avs).
  unfold dontReuse; induction avs; inversion_clear 1; simpl; intuition.
  apply himp_star_frame; auto.
  unfold cvars in *; simpl in *; intuition idtac;
    unfold cursor; apply himp_star_frame;
      repeat match goal with
               | [ V : vals |- _ ] =>
                 progress repeat match goal with
                                   | [ |- context[V ?x] ] => change (V x) with (sel V x)
                                 end
             end;
      try match goal with
            | [ H : forall x : string, _ |- _ ] => repeat rewrite H by congruence
          end; reflexivity.
Qed.

Hint Resolve weaken_cursors'.

Lemma twfs_removeTable : forall x ts,
  twfs ts
  -> twfs (removeTable x ts).
  unfold twfs; induction 1; simpl; intuition; ift.
Qed.

Hint Constructors NoDup.

Lemma In_removeTable : forall x y ts,
  In x (Names (removeTable y ts))
  -> In x (Names ts).
  induction ts; simpl; intuition idtac;
    match goal with
      | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; simpl in *; tauto
    end.
Qed.

Hint Immediate In_removeTable.

Lemma NoDup_removeTable : forall x ts,
  NoDup (Names ts)
  -> NoDup (Names (removeTable x ts)).
  induction ts; inversion_clear 1; simpl; intuition;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E; simpl; eauto
    end.
Qed.

Hint Immediate twfs_removeTable NoDup_removeTable.

Hint Extern 1 (goodCursors _) =>
  apply Forall_cons; try assumption; simpl; tauto.

Hint Extern 1 (incl _ _) => hnf; simpl; intuition congruence.

Lemma cwf_wfEqualities : forall sch cdatas ns cond,
  cwf ns sch cdatas cond
  -> wfEqualities ns sch cond.
  clear; unfold wfEqualities; induction 1; simpl; intuition.
  constructor; auto.
  unfold wfEquality, eqwf in *; destruct x as [ ? [ ] ]; simpl in *; tauto.
Qed.

Hint Immediate cwf_wfEqualities.

Lemma goodSize_base : forall t ts,
  twfs ts
  -> In t ts
  -> goodSize (length (Schema t)).
  intros ? ? H H0; eapply Forall_forall in H; [ | eassumption ]; unfold twf in *; intuition idtac.
  eapply goodSize_weaken; eauto.
Qed.

Hint Immediate goodSize_base.

Lemma cwf_noOverlapExps : forall ns rw data cdatas sch cond,
  cwf ns sch cdatas cond
  -> dontTouch rw data cdatas
  -> noOverlapExps rw data (exps cond).
  unfold dontTouch, noOverlapExps, noOverlapExp, eqwf; induction 1; simpl; intuition.
  constructor; auto.
  unfold eqwf in *; intuition.
  destruct (snd x); unfold ewf in *; intuition subst;
    (eapply ForallR_Forall in H1; eapply Forall_forall in H1; [ | eassumption ];
      simpl in *; tauto).
Qed.

Hint Immediate cwf_noOverlapExps.

Definition NoDups (avs : list avail) (ts : tables) :=
  NoDup (map (fun av => Name (Table av)) avs ++ Names ts).

Lemma NoDups_ts : forall avs ts,
  NoDups avs ts
  -> NoDup (Names ts).
  intros; eapply NoDup_unapp2; eauto.
Qed.

Lemma NoDups_avs : forall avs ts,
  NoDups avs ts
  -> NoDup (map (fun av => Name (Table av)) avs).
  intros; eapply NoDup_unapp1; eauto.
Qed.

Hint Immediate NoDups_ts NoDups_avs.

Lemma goodCursors_removeCursor : forall tab avs,
  goodCursors avs
  -> goodCursors (removeCursor tab avs).
  unfold goodCursors; induction 1; simpl; intuition; ift.
Qed.

Hint Immediate goodCursors_removeCursor.

Lemma goodCursors_cons : forall t rw data avs,
  goodCursors avs
  -> ~In rw cvars
  -> ~In data cvars
  -> goodSize (length (Schema t))
  -> goodCursors ({| Table := t; Row := rw; Data := data |} :: avs).
  clear; intros; constructor; intuition.
Qed.

Hint Extern 1 (goodCursors (_ :: _)) => eapply goodCursors_cons; eauto 2; (simpl; tauto).

Lemma NoDups_app : forall A (ls1 ls2 : list A),
  NoDup ls1
  -> NoDup ls2
  -> (forall x, In x ls1 -> ~In x ls2)
  -> NoDup (ls1 ++ ls2).
  clear; induction 1; simpl; intuition.
  constructor; eauto.
  intro.
  apply in_app_or in H4; intuition eauto.
Qed.

Lemma NoDups_unapp_cross : forall A (ls1 ls2 : list A),
  NoDup (ls1 ++ ls2)
  -> (forall x, In x ls1 -> ~In x ls2).
  clear; induction ls1; inversion_clear 1; simpl; intuition eauto.
  subst.
  apply H0.
  apply in_or_app; tauto.
Qed.

Lemma removeTable_contra : forall tab ts,
  NoDup (Names ts)
  -> In tab (Names (removeTable tab ts))
  -> False.
  clear; induction ts; inversion_clear 1; simpl; intuition.
  destruct (string_dec tab (Name a)); subst; simpl in *; intuition.
Qed.

Lemma NoDups_move : forall avs ts t rw data,
  In t ts
  -> NoDups avs ts
  -> NoDups ({| Table := t; Row := rw; Data := data |} :: avs) (removeTable (Name t) ts).
  clear; unfold NoDups; intros; simpl.
  constructor.
  intro.
  apply in_app_or in H1; intuition eauto using removeTable_contra.
  specialize (NoDups_unapp_cross _ _ H0 _ H2); intro.
  apply H1.
  apply in_map; auto.
  apply NoDups_app; eauto using NoDup_removeTable.
  intros.
  intro.
  eapply NoDups_unapp_cross in H0; eauto.
Qed.

Hint Immediate NoDups_move.

Module Type TO_CMD.
  Parameter toCmd' : chunk ->
    forall (im : LabelMap.t assert) (mn : string),
      importsGlobal im -> list string -> nat -> cmd im mn.

  Axiom toCmd'_eq : toCmd' = toCmd.
End TO_CMD.

Module ToCmd : TO_CMD.
  Definition toCmd' := toCmd.

  Theorem toCmd'_eq : toCmd' = toCmd.
    auto.
  Qed.
End ToCmd.

Import ToCmd.

Definition clarify (ch : chunk) : chunk := fun ns n =>
  Structured nil (fun im mn H => toCmd' ch mn H ns n).


(** * Compiling XML snippets into Bedrock chunks *)

Section Out.
  Variable A : Type.
  Variable invPre : A -> vals -> HProp.
  Variable invPost : A -> vals -> W -> HProp.

  (* Precondition and postcondition of generation *)
  Definition invar cdatas avs ts :=
    Al a : A, Al bsI, Al bsO,
    PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
      * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
      * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]
      * cursors V avs * db ts * invPre a V
    POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
      * [| length bsO' = length bsO |] * invPost a V R.

  Infix ";;" := SimpleSeq : SP_scope.

  Section OutList.
    Variable Out' : xml -> chunk.

    Fixpoint OutList (xms : list xml) : chunk :=
      match xms with
        | nil => Skip
        | xm :: xms' => (Out' xm;; OutList xms')
      end%SP.
  End OutList.

  Inductive reveal_row : Prop := RevealRow.
  Hint Constructors reveal_row.

  Fixpoint Out' (cdatas : list (string * string)) (avs : list avail) (ts : list table) (xm : xml) : chunk :=
    match xm with
      | Cdata const => StringWrite "obuf" "olen" "opos" "overflowed" const
        (fun (p : list B * A) V => array8 (fst p) (V "buf") * [| length (fst p) = wordToNat (V "len") |]
          * [| inBounds cdatas V |] * invPre (snd p) V * cursors V avs * db ts)%Sep
        (fun _ (p : list B * A) V R => Ex bs', array8 bs' (V "obuf") * [| length bs' = wordToNat (V "olen") |]
          * array8 (fst p) (V "buf") * invPost (snd p) V R)%Sep

      | Var start len =>
        "tmp" <- "olen" - "opos";;
        If (len < "tmp") {
          Call "array8"!"copy"("obuf", "opos", "buf", start, len)
          [Al a : A, Al bsI, Al bsO,
            PRE[V] [| V len < V "olen" ^- V "opos" |]%word * array8 bsI (V "buf") * array8 bsO (V "obuf")
              * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
              * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word
              * invPre a V * cursors V avs * db ts
            POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf") * [| length bsO' = length bsO |]
              * invPost a V R];;
          "opos" <- "opos" + len
        } else {
          "overflowed" <- 1
        }

      | Tag tag inner =>
        StringWrite "obuf" "olen" "opos" "overflowed" ("<" ++ tag ++ ">")
        (fun (p : list B * A) V => array8 (fst p) (V "buf") * [| length (fst p) = wordToNat (V "len") |]
          * invPre (snd p) V * [| inBounds cdatas V |] * cursors V avs * db ts)%Sep
        (fun _ (p : list B * A) V R => Ex bs', array8 bs' (V "obuf") * [| length bs' = wordToNat (V "olen") |]
          * array8 (fst p) (V "buf") * invPost (snd p) V R)%Sep;;
        OutList (Out' cdatas avs ts) inner;;
        StringWrite "obuf" "olen" "opos" "overflowed" ("</" ++ tag ++ ">")
        (fun (p : list B * A) V => array8 (fst p) (V "buf") * [| length (fst p) = wordToNat (V "len") |]
          * invPre (snd p) V * [| inBounds cdatas V |] * cursors V avs * db ts)%Sep
        (fun _ (p : list B * A) V R => Ex bs', array8 bs' (V "obuf") * [| length bs' = wordToNat (V "olen") |]
          * array8 (fst p) (V "buf") * invPost (snd p) V R)%Sep

      | Column tab col =>
        match findCursor tab avs with
          | None => Fail
          | Some av =>
            Assert [Al a : A, Al bsI, Al bsO,
              PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
                * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
                * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word
                * cursor V av * cursors V (removeCursor tab avs) * db ts * invPre a V
              POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
                * [| length bsO' = length bsO |] * invPost a V R];;

            Note [reveal_row];;

            Assert [Al a : A, Al bsI, Al bsO,
              PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
                * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
                * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word * invPre a V
                * cursors V (removeCursor tab avs) * db ts
                * RelDbSelect.inv (Address (Table av)) (Schema (Table av)) (V (Row av)) (V (Data av))
                * Ex buf, Ex len, Ex cols, Ex bs,
                  (V (Data av) ==*> buf, len) * array (posl cols) (V (Data av) ^+ $8)
                  * array (lenl cols) (V (Data av) ^+ $8 ^+ $ (length (Schema (Table av)) * 4)) * array8 bs buf
                  * [| length bs = wordToNat len |] * [| length cols = length (Schema (Table av)) |]
                  * [| RelDb.inBounds len cols |]
                  * [| V (Data av) <> 0 |]
                  * [| freeable (V (Data av)) (2 + length (Schema (Table av)) + length (Schema (Table av))) |]
                  * [| buf <> 0 |] * [| freeable8 buf (length bs) |]
                  * [| natToW (findCol (Schema (Table av)) col) < natToW (length (lenl cols)) |]%word
              POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
                * [| length bsO' = length bsO |] * invPost a V R];;

            "matched" <- Data av + 8;;
            "matched" <- "matched" + (length (Schema (Table av)) * 4)%nat;;
            "matched" <-* "matched" + (4 * findCol (Schema (Table av)) col)%nat;;

            "tmp" <- "olen" - "opos";;
            Note [reveal_row];;
            If ("matched" < "tmp") {
              Assert [Al a : A, Al bsI, Al bsO,
                PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
                  * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
                  * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word * invPre a V
                  * cursors V (removeCursor tab avs) * db ts
                  * RelDbSelect.inv (Address (Table av)) (Schema (Table av)) (V (Row av)) (V (Data av))
                  * Ex buf, Ex len, Ex cols, Ex bs,
                    (V (Data av) ==*> buf, len) * array (posl cols) (V (Data av) ^+ $8)
                    * array (lenl cols) (V (Data av) ^+ $8 ^+ $ (length (Schema (Table av)) * 4)) * array8 bs buf
                    * [| length bs = wordToNat len |] * [| length cols = length (Schema (Table av)) |]
                    * [| RelDb.inBounds len cols |]
                    * [| V (Data av) <> 0 |]
                    * [| freeable (V (Data av)) (2 + length (Schema (Table av)) + length (Schema (Table av))) |]
                    * [| buf <> 0 |] * [| freeable8 buf (length bs) |]
                    * [| V "matched" = Array.selN (lenl cols) (findCol (Schema (Table av)) col) |]
                    * [| natToW (findCol (Schema (Table av)) col) < natToW (length (posl cols)) |]%word
                    * [| V "matched" < V "olen" ^- V "opos" |]%word
                POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
                  * [| length bsO' = length bsO |] * invPost a V R];;

              "tmp" <- Data av + 8;;
              "tmp" <-* "tmp" + (4 * findCol (Schema (Table av)) col)%nat;;
              Note [reveal_row];;

              Assert [Al a : A, Al bsI, Al bsO,
                PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
                  * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
                  * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word * invPre a V
                  * cursors V (removeCursor tab avs) * db ts
                  * RelDbSelect.inv (Address (Table av)) (Schema (Table av)) (V (Row av)) (V (Data av))
                  * Ex buf, Ex len, Ex cols, Ex bs,
                    (V (Data av) ==*> buf, len) * array (posl cols) (V (Data av) ^+ $8)
                    * array (lenl cols) (V (Data av) ^+ $8 ^+ $ (length (Schema (Table av)) * 4)) * array8 bs buf
                    * [| length bs = wordToNat len |] * [| length cols = length (Schema (Table av)) |]
                    * [| RelDb.inBounds len cols |]
                    * [| V (Data av) <> 0 |]
                    * [| freeable (V (Data av)) (2 + length (Schema (Table av)) + length (Schema (Table av))) |]
                    * [| buf <> 0 |] * [| freeable8 buf (length bs) |]
                    * [| V "matched" = Array.selN (lenl cols) (findCol (Schema (Table av)) col) |]
                    * [| V "tmp" = Array.selN (posl cols) (findCol (Schema (Table av)) col) |]
                    * [| V "matched" < V "olen" ^- V "opos" |]%word
                POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
                  * [| length bsO' = length bsO |] * invPost a V R];;

              Note [reveal_row];;
              "res" <-* Data av;;

              Call "array8"!"copy"("obuf", "opos", "res", "tmp", "matched")
              [Al a : A, Al bsI, Al bsO,
                PRE[V] [| V "matched" < V "olen" ^- V "opos" |]%word
                  * array8 bsI (V "buf") * array8 bsO (V "obuf")
                  * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
                  * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word
                  * invPre a V * cursors V avs * db ts
                POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf") * [| length bsO' = length bsO |]
                  * invPost a V R];;
              "opos" <- "opos" + "matched"
            } else {
              Note [reveal_row];;

              "overflowed" <- 1
            }
        end

      | Select tab rw data cond inner =>
        match findTable tab ts with
          | None => Fail
          | Some t => RelDbSelect.Select
            (fun (p : list B * A) V => cursors V avs
              * db (removeTable tab ts)
              * array8 (fst p) (V "obuf")
              * [| length (fst p) = wordToNat (V "olen") |]
              * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word
              * invPre (snd p) V)%Sep
            (fun p V R => Ex bsO', array8 bsO' (V "obuf") * [| length bsO' = length (fst p) |]
              * invPost (snd p) V R)%Sep
            (Address t) (Schema t) rw data cond
            (Out' cdatas
              ({| Table := t; Row := rw; Data := data |} :: avs)
              (removeTable tab ts)
              inner)
        end

      | IfEqual tab1 col1 tab2 col2 inner =>
        match findCursor tab1 avs, findCursor tab2 avs with
          | Some av1, Some av2 =>
            If ("overflowed" = 0) {
              Assert [Al a : A, Al bsI, Al bsO,
                PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
                  * [| length bsI = wordToNat (V "len") |]
                  * [| length bsO = wordToNat (V "olen") |]
                  * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word
                  * cursor V av1 * cursor V av2
                  * cursors V (removeCursor tab2 (removeCursor tab1 avs))
                  * db ts * invPre a V
                POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
                  * [| length bsO' = length bsO |] * invPost a V R];;

              Note [reveal_row];;

              Assert [Al a : A, Al bsI, Al bsO,
                PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
                  * [| length bsI = wordToNat (V "len") |]
                  * [| length bsO = wordToNat (V "olen") |]
                  * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word
                  * invPre a V
                  * cursors V (removeCursor tab2 (removeCursor tab1 avs)) * db ts
                  * RelDbSelect.inv (Address (Table av1)) (Schema (Table av1))
                  (V (Row av1)) (V (Data av1))
                  * RelDbSelect.inv (Address (Table av2)) (Schema (Table av2))
                  (V (Row av2)) (V (Data av2))
                  * (Ex buf1, Ex len1, Ex cols1, Ex bs1,
                    (V (Data av1) ==*> buf1, len1)
                    * array (posl cols1) (V (Data av1) ^+ $8)
                    * array (lenl cols1) (V (Data av1) ^+ $8
                      ^+ $ (length (Schema (Table av1)) * 4)) * array8 bs1 buf1
                    * [| length bs1 = wordToNat len1 |]
                    * [| length cols1 = length (Schema (Table av1)) |]
                    * [| RelDb.inBounds len1 cols1 |]
                    * [| V (Data av1) <> 0 |]
                    * [| freeable (V (Data av1))
                      (2 + length (Schema (Table av1))
                        + length (Schema (Table av1))) |]
                    * [| buf1 <> 0 |] * [| freeable8 buf1 (length bs1) |]
                    * [| natToW (findCol (Schema (Table av1)) col1)
                      < natToW (length (lenl cols1)) |]%word)
                  * (Ex buf2, Ex len2, Ex cols2, Ex bs2,
                    (V (Data av2) ==*> buf2, len2)
                    * array (posl cols2) (V (Data av2) ^+ $8)
                    * array (lenl cols2) (V (Data av2) ^+ $8
                      ^+ $ (length (Schema (Table av2)) * 4)) * array8 bs2 buf2
                    * [| length bs2 = wordToNat len2 |]
                    * [| length cols2 = length (Schema (Table av2)) |]
                    * [| RelDb.inBounds len2 cols2 |]
                    * [| V (Data av2) <> 0 |]
                    * [| freeable (V (Data av2))
                      (2 + length (Schema (Table av2))
                        + length (Schema (Table av2))) |]
                    * [| buf2 <> 0 |] * [| freeable8 buf2 (length bs2) |]
                    * [| natToW (findCol (Schema (Table av2)) col2)
                      < natToW (length (lenl cols2)) |]%word)
                POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
                  * [| length bsO' = length bsO |] * invPost a V R];;

              "matched" <- Data av1 + 8;;
              "matched" <- "matched" + (length (Schema (Table av1)) * 4)%nat;;
              "matched" <-* "matched" + (4 * findCol (Schema (Table av1)) col1)%nat;;

              Assert [Al a : A, Al bsI, Al bsO,
                PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
                  * [| length bsI = wordToNat (V "len") |]
                  * [| length bsO = wordToNat (V "olen") |]
                  * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word
                  * invPre a V
                  * cursors V (removeCursor tab2 (removeCursor tab1 avs)) * db ts
                  * RelDbSelect.inv (Address (Table av1)) (Schema (Table av1))
                  (V (Row av1)) (V (Data av1))
                  * RelDbSelect.inv (Address (Table av2)) (Schema (Table av2))
                  (V (Row av2)) (V (Data av2))
                  * (Ex buf1, Ex len1, Ex cols1, Ex bs1,
                    (V (Data av1) ==*> buf1, len1)
                    * array (posl cols1) (V (Data av1) ^+ $8)
                    * array (lenl cols1) (V (Data av1) ^+ $8
                      ^+ $ (length (Schema (Table av1)) * 4)) * array8 bs1 buf1
                    * [| length bs1 = wordToNat len1 |]
                    * [| length cols1 = length (Schema (Table av1)) |]
                    * [| RelDb.inBounds len1 cols1 |]
                    * [| V (Data av1) <> 0 |]
                    * [| freeable (V (Data av1))
                      (2 + length (Schema (Table av1))
                        + length (Schema (Table av1))) |]
                    * [| buf1 <> 0 |] * [| freeable8 buf1 (length bs1) |]
                    * [| V "matched" = Array.selN (lenl cols1)
                        (findCol (Schema (Table av1)) col1) |])
                  * (Ex buf2, Ex len2, Ex cols2, Ex bs2,
                    (V (Data av2) ==*> buf2, len2)
                    * array (posl cols2) (V (Data av2) ^+ $8)
                    * array (lenl cols2) (V (Data av2) ^+ $8
                      ^+ $ (length (Schema (Table av2)) * 4)) * array8 bs2 buf2
                    * [| length bs2 = wordToNat len2 |]
                    * [| length cols2 = length (Schema (Table av2)) |]
                    * [| RelDb.inBounds len2 cols2 |]
                    * [| V (Data av2) <> 0 |]
                    * [| freeable (V (Data av2))
                      (2 + length (Schema (Table av2))
                        + length (Schema (Table av2))) |]
                    * [| buf2 <> 0 |] * [| freeable8 buf2 (length bs2) |]
                    * [| natToW (findCol (Schema (Table av2)) col2)
                      < natToW (length (lenl cols2)) |]%word)
                POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
                  * [| length bsO' = length bsO |] * invPost a V R];;

              "tmp" <- Data av2 + 8;;
              "tmp" <- "tmp" + (length (Schema (Table av2)) * 4)%nat;;
              "tmp" <-* "tmp" + (4 * findCol (Schema (Table av2)) col2)%nat;;

              Note [reveal_row];;
              If ("matched" = "tmp") {
                Assert [Al a : A, Al bsI, Al bsO,
                  PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
                    * [| length bsI = wordToNat (V "len") |]
                    * [| length bsO = wordToNat (V "olen") |]
                    * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word
                    * invPre a V
                    * cursors V (removeCursor tab2 (removeCursor tab1 avs))
                    * db ts
                    * RelDbSelect.inv (Address (Table av1)) (Schema (Table av1))
                    (V (Row av1)) (V (Data av1))
                    * RelDbSelect.inv (Address (Table av2)) (Schema (Table av2))
                    (V (Row av2)) (V (Data av2))
                    * (Ex buf1, Ex len1, Ex cols1, Ex bs1,
                      (V (Data av1) ==*> buf1, len1)
                      * array (posl cols1) (V (Data av1) ^+ $8)
                      * array (lenl cols1) (V (Data av1) ^+ $8
                        ^+ $ (length (Schema (Table av1)) * 4)) * array8 bs1 buf1
                      * [| length bs1 = wordToNat len1 |]
                      * [| length cols1 = length (Schema (Table av1)) |]
                      * [| RelDb.inBounds len1 cols1 |]
                      * [| V (Data av1) <> 0 |]
                      * [| freeable (V (Data av1)) (2
                        + length (Schema (Table av1))
                        + length (Schema (Table av1))) |]
                      * [| buf1 <> 0 |] * [| freeable8 buf1 (length bs1) |]
                      * [| V "matched" = Array.selN (lenl cols1)
                        (findCol (Schema (Table av1)) col1) |]
                      * [| natToW (findCol (Schema (Table av1)) col1)
                        < natToW (length (posl cols1)) |]%word)
                    * (Ex buf2, Ex len2, Ex cols2, Ex bs2,
                      (V (Data av2) ==*> buf2, len2)
                      * array (posl cols2) (V (Data av2) ^+ $8)
                      * array (lenl cols2) (V (Data av2) ^+ $8
                        ^+ $ (length (Schema (Table av2)) * 4)) * array8 bs2 buf2
                      * [| length bs2 = wordToNat len2 |]
                      * [| length cols2 = length (Schema (Table av2)) |]
                      * [| RelDb.inBounds len2 cols2 |]
                      * [| V (Data av2) <> 0 |]
                      * [| freeable (V (Data av2)) (2
                        + length (Schema (Table av2))
                        + length (Schema (Table av2))) |]
                      * [| buf2 <> 0 |] * [| freeable8 buf2 (length bs2) |]
                      * [| V "tmp" = Array.selN (lenl cols2)
                        (findCol (Schema (Table av2)) col2) |]
                      * [| natToW (findCol (Schema (Table av2)) col2)
                        < natToW (length (posl cols2)) |]%word)
                    * [| V "matched" = V "tmp"|]%word
                  POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
                    * [| length bsO' = length bsO |] * invPost a V R];;

                "tmp" <- Data av1 + 8;;
                "tmp" <-* "tmp" + (4 * findCol (Schema (Table av1)) col1)%nat;;

                Assert [Al a : A, Al bsI, Al bsO,
                  PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
                    * [| length bsI = wordToNat (V "len") |]
                    * [| length bsO = wordToNat (V "olen") |]
                    * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word
                    * invPre a V
                    * cursors V (removeCursor tab2 (removeCursor tab1 avs))
                    * db ts
                    * RelDbSelect.inv (Address (Table av1)) (Schema (Table av1))
                    (V (Row av1)) (V (Data av1))
                    * RelDbSelect.inv (Address (Table av2)) (Schema (Table av2))
                    (V (Row av2)) (V (Data av2))
                    * (Ex buf1, Ex len1, Ex cols1, Ex bs1,
                      (V (Data av1) ==*> buf1, len1)
                      * array (posl cols1) (V (Data av1) ^+ $8)
                      * array (lenl cols1) (V (Data av1) ^+ $8
                        ^+ $ (length (Schema (Table av1)) * 4)) * array8 bs1 buf1
                      * [| length bs1 = wordToNat len1 |]
                      * [| length cols1 = length (Schema (Table av1)) |]
                      * [| RelDb.inBounds len1 cols1 |]
                      * [| V (Data av1) <> 0 |]
                      * [| freeable (V (Data av1)) (2
                        + length (Schema (Table av1))
                        + length (Schema (Table av1))) |]
                      * [| buf1 <> 0 |] * [| freeable8 buf1 (length bs1) |]
                      * [| V "matched" = Array.selN (lenl cols1)
                        (findCol (Schema (Table av1)) col1) |]
                      * [| V "tmp" = Array.selN (posl cols1)
                        (findCol (Schema (Table av1)) col1) |])
                    * (Ex buf2, Ex len2, Ex cols2, Ex bs2,
                      (V (Data av2) ==*> buf2, len2)
                      * array (posl cols2) (V (Data av2) ^+ $8)
                      * array (lenl cols2) (V (Data av2) ^+ $8
                        ^+ $ (length (Schema (Table av2)) * 4)) * array8 bs2 buf2
                      * [| length bs2 = wordToNat len2 |]
                      * [| length cols2 = length (Schema (Table av2)) |]
                      * [| RelDb.inBounds len2 cols2 |]
                      * [| V (Data av2) <> 0 |]
                      * [| freeable (V (Data av2)) (2
                        + length (Schema (Table av2))
                        + length (Schema (Table av2))) |]
                      * [| buf2 <> 0 |] * [| freeable8 buf2 (length bs2) |]
                      * [| V "matched" = Array.selN (lenl cols2)
                        (findCol (Schema (Table av2)) col2) |]
                      * [| natToW (findCol (Schema (Table av2)) col2)
                        < natToW (length (posl cols2)) |]%word)
                  POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
                    * [| length bsO' = length bsO |] * invPost a V R];;

                "res" <- Data av2 + 8;;
                "res" <-* "res" + (4 * findCol (Schema (Table av2)) col2)%nat;;

                Note [reveal_row];;

                Assert [Al a : A, Al bsI, Al bsO,
                  PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
                    * [| length bsI = wordToNat (V "len") |]
                    * [| length bsO = wordToNat (V "olen") |]
                    * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word
                    * invPre a V
                    * cursors V (removeCursor tab2 (removeCursor tab1 avs)) * db ts
                    * RelDbSelect.inv (Address (Table av1)) (Schema (Table av1))
                    (V (Row av1)) (V (Data av1))
                    * RelDbSelect.inv (Address (Table av2)) (Schema (Table av2))
                    (V (Row av2)) (V (Data av2))
                    * (Ex buf1, Ex len1, Ex cols1, Ex bs1,
                      (V (Data av1) ==*> buf1, len1)
                      * array (posl cols1) (V (Data av1) ^+ $8)
                      * array (lenl cols1) (V (Data av1) ^+ $8
                        ^+ $ (length (Schema (Table av1)) * 4)) * array8 bs1 buf1
                      * [| length bs1 = wordToNat len1 |]
                      * [| length cols1 = length (Schema (Table av1)) |]
                      * [| RelDb.inBounds len1 cols1 |]
                      * [| V (Data av1) <> 0 |]
                      * [| freeable (V (Data av1)) (2
                        + length (Schema (Table av1))
                        + length (Schema (Table av1))) |]
                      * [| buf1 <> 0 |] * [| freeable8 buf1 (length bs1) |]
                      * [| V "matched" = Array.selN (lenl cols1)
                        (findCol (Schema (Table av1)) col1) |]
                      * [| V "tmp" = Array.selN (posl cols1)
                        (findCol (Schema (Table av1)) col1) |])
                    * (Ex buf2, Ex len2, Ex cols2, Ex bs2,
                      (V (Data av2) ==*> buf2, len2)
                      * array (posl cols2) (V (Data av2) ^+ $8)
                      * array (lenl cols2) (V (Data av2) ^+ $8
                        ^+ $ (length (Schema (Table av2)) * 4)) * array8 bs2 buf2
                      * [| length bs2 = wordToNat len2 |]
                      * [| length cols2 = length (Schema (Table av2)) |]
                      * [| RelDb.inBounds len2 cols2 |]
                      * [| V (Data av2) <> 0 |]
                      * [| freeable (V (Data av2)) (2
                        + length (Schema (Table av2))
                        + length (Schema (Table av2))) |]
                      * [| buf2 <> 0 |] * [| freeable8 buf2 (length bs2) |]
                      * [| V "matched" = Array.selN (lenl cols2)
                        (findCol (Schema (Table av2)) col2) |]
                      * [| V "res" = Array.selN (posl cols2)
                        (findCol (Schema (Table av2)) col2) |])
                  POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
                    * [| length bsO' = length bsO |] * invPost a V R];;

                Note [reveal_row];;
                Rp <-* Data av2;;
                "overflowed" <-* Data av1;;

                "res" <-- Call "array8"!"equal"("overflowed", "tmp", Rp, "res", "matched")
                [Al a : A, Al bsI, Al bsO,
                  PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
                    * [| length bsI = wordToNat (V "len") |]
                    * [| length bsO = wordToNat (V "olen") |]
                    * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word
                    * invPre a V * cursors V avs * db ts
                  POST[R] Ex bsO', array8 bsI (V "buf")
                    * array8 bsO' (V "obuf") * [| length bsO' = length bsO |]
                    * invPost a V R];;

                "overflowed" <- 0;;

                If ("res" = 1) {
                  clarify (Out' cdatas avs ts inner)
                } else {
                  Skip
                }
              } else {
                Note [reveal_row]
              }
            } else {
              Skip
            }
          | _, _ => Fail
        end
    end%SP.

  Opaque mult.

  Lemma invPre_sel : forall a V, invPre a (sel V) = invPre a V.
    auto.
  Qed.

  Lemma invPost_sel : forall a V R, invPost a (sel V) R = invPost a V R.
    auto.
  Qed.

  Lemma inBounds_sel : forall cdatas V, inBounds cdatas (sel V) = inBounds cdatas V.
    auto.
  Qed.

  Lemma cursors_sel : forall V av, cursors (sel V) av = cursors V av.
    auto.
  Qed.

  Lemma cursor_sel : forall V av, cursor (sel V) av = cursor V av.
    auto.
  Qed.

  Ltac prep :=
    clear_fancy; repeat match goal with
                          | [ H : LabelMap.find _ _ = _ |- _ ] => try rewrite H; clear H
                          | [ st : (settings * state)%type |- _ ] => destruct st; simpl in *
                        end;
    try match goal with
          | [ _ : context[reveal_row] |- _ ] => unfold cursor, row in *
        end.

  Ltac reger := repeat match goal with
                         | [ H : Regs _ _ = _ |- _ ] => rewrite H
                       end.

  Ltac my_refold :=
    refold;
    fold (@length B) in *; fold (@length string) in *;
      fold (@length (W * W)) in *; fold (@length W) in *.

  Ltac simp :=
    repeat match goal with
             | [ H : context[invPre ?a (sel ?V)] |- _ ] => rewrite (invPre_sel a V) in H
             | [ |- context[invPre ?a (sel ?V)] ] => rewrite (invPre_sel a V)
             | [ H : context[invPost ?a (sel ?V) ?R] |- _ ] => rewrite (invPost_sel a V R) in H
             | [ |- context[invPost ?a (sel ?V) ?R] ] => rewrite (invPost_sel a V R)
             | [ H : context[inBounds ?x (sel ?V)] |- _ ] => rewrite (inBounds_sel x V) in H
             | [ |- context[inBounds ?x (sel ?V)] ] => rewrite (inBounds_sel x V)
             | [ H : context[cursors (sel ?V) ?x] |- _ ] => rewrite (cursors_sel V x) in H
             | [ |- context[cursors (sel ?V) ?x] ] => rewrite (cursors_sel V x)
             | [ H : context[cursor (sel ?V) ?x] |- _ ] => rewrite (cursor_sel V x) in H
             | [ |- context[cursor (sel ?V) ?x] ] => rewrite (cursor_sel V x)
             | [ H : context[inputOk (sel ?V) ?x] |- _ ] => rewrite (inputOk_sel V x) in H
             | [ |- context[inputOk (sel ?V) ?x] ] => rewrite (inputOk_sel V x)
           end; reger.

  Ltac prepl := post; unfold lvalIn, regInL, immInR in *;
    repeat match goal with
             | [ H : ForallR _ _ |- _ ] => clear H
             | [ H : List.Forall _ _ |- _ ] => clear H
             | [ H : importsGlobal _ |- _ ] =>
               repeat match goal with
                        | [ H' : context[H] |- _ ] => clear H'
                      end; clear H
           end; prep_locals; simp; try rewrite mult4_S in *;
    try match goal with
          | [ H : cdatasGood _, H' : In _ _ |- _ ] =>
            specialize (proj1 (Forall_forall _ _) H _ H'); simpl; intuition idtac
        end;
    try rewrite natToW_4times in *.

  Ltac my_descend :=
    try match goal with
          | [ H : inBounds _ _, H' : In _ _ |- _ ] =>
            rewrite <- inBounds_sel in H;
              specialize (proj1 (Forall_forall _ _) H _ H'); simpl; intuition idtac;
                rewrite inBounds_sel in H
        end;
    repeat match goal with
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
             | [ H : evalCond _ _ _ _ _ = _ |- _ ] => clear H
             | [ H : In _ ?ls |- _ ] =>
               match type of ls with
                 | schema => fail 1
                 | list table => fail 1
                 | list avail => fail 1
                 | _ => clear H
               end
             | [ x : (_ * _)%type |- _ ] => destruct x; simpl in *
           end;
    unfold invar, localsInvariant; descend;
      simp; reger;
      try match goal with
            | [ |- context[match ?U with pair _ _ => _ end] ] =>
              match type of U with
                | prod ?A ?B =>
                  let x := fresh in let y := fresh in
                    evar (x : A); evar (y : B); let x' := eval unfold x in x in
                      let y' := eval unfold y in y in equate U (x', y'); clear x y; simpl
              end
          end; autorewrite with sepFormula in *; my_refold.

  Ltac deSpec :=
    repeat match goal with
             | [ H : LabelMap.find _ _ = _ |- _ ] => try rewrite H; clear H
           end.

  Ltac invoke1 :=
    match goal with
      | [ H : interp _ _, H' : _ |- _ ] => apply H' in H; clear H'
      | [ |- vcs (_ :: _) ] => wrap0; try discriminate
      | [ H : _ |- vcs _ ] => apply vcs_app_fwd || apply H
    end; post.

  Lemma cursor_wiggle : forall V' V P avs a,
    goodCursors avs
    -> (forall x, x <> "overflowed" -> x <> "opos" ->
      x <> "tmp" -> x <> "matched" -> x <> "res" -> sel V x = sel V' x)
    -> invPre a V ===> invPre a V'
    -> invPre a V * (cursors V avs * P)
    ===> P * (invPre a V' * cursors V' avs).
    clear; sepLemma; apply himp_star_frame.
    apply weaken_cursors; auto.
    auto.
  Qed.

  Ltac bash :=
    try match goal with
          | [ H : context[invPost] |- ?P = ?Q ] =>
            match P with
              | context[invPost ?a ?V _] =>
                match Q with
                  | context[invPost a ?V' _] =>
                    rewrite (H a V V') by intuition; reflexivity
                end
            end
        end;

    match goal with
      | [ |- interp _ (![?pre] _ ---> ![?post] _)%PropX ] =>
        match post with
          | context[locals ?ns ?vs ?avail _] =>
            match pre with
              | context[excessStack _ ns avail ?ns' ?avail'] =>
                match avail' with
                  | avail => fail 1
                  | _ =>
                    match pre with
                      | context[locals ns ?vs' 0 ?sp] =>
                        match goal with
                          | [ _ : _ = sp |- _ ] => fail 1
                          | _ => equate vs vs';
                            let offset := eval simpl in (4 * List.length ns) in
                              rewrite (create_locals_return ns' avail' ns avail offset);
                                assert (ok_return ns ns' avail avail' offset)%nat by (split; [
                                  simpl; omega
                                  | reflexivity ] ); autorewrite with sepFormula in *;
                                cancel auto_ext
                        end
                    end
                end
            end
        end
      | _ => weaken_invPre
      | [ _ : context[reveal_row] |- _ ] => try match_locals; step RelDb.hints
      | _ => try match_locals; step auto_ext
    end;
    try (apply removeTable_bwd'; solve [ eauto ]);
    try (apply removeTable_fwd'; solve [ eauto ]);
    try apply make_cursor; try apply unmake_cursor;
    try (apply matchup; solve [ auto ]);
    try (apply matchup2; solve [ auto ]);
    try (apply cursor_wiggle; solve [ descend; try apply goodCursors_removeCursor; auto ]);
    try (etransitivity; [ apply himp_star_comm | ]; apply himp_star_frame; try reflexivity;
      apply release_cursor; eauto);
    try (etransitivity; [ | (apply cursor_expand || apply cursor_expand'); try eassumption ];
      match goal with
        | [ |- himp _ _ _ ] => unfold row; simpl; bash
        | _ => descend; eauto
      end).

  Ltac desc := my_descend;
    [ try match goal with
            | [ _ : context[reveal_row], H : goodCursors _, H' : In _ _ |- _ ] =>
              destruct (proj1 (Forall_forall _ _) H _ H');
                simpl in *; intuition idtac
          end | .. ].

  Ltac t := post; repeat invoke1; prep; propxFo;
    repeat invoke1; prepl; evaluate auto_ext;
      desc; (repeat (bash; my_descend); eauto).

  Notation "l ~~ im ~~> s" := (LabelMap.find l%SP im = Some (Precondition s None)) (at level 0).

  Section Out_correct.
    Variables (ns : list string) (res : nat).

    Hypothesis Hrp : ~In "rp" ns.
    Hypothesis Hobuf : In "obuf" ns.
    Hypothesis Holen : In "olen" ns.
    Hypothesis Hopos : In "opos" ns.
    Hypothesis Hoverflowed : In "overflowed" ns.
    Hypothesis Htmp : In "tmp" ns.
    Hypothesis Hbuf : In "buf" ns.
    Hypothesis Hmatched : In "matched" ns.
    Hypothesis HresV : In "res" ns.

    Hypothesis Hres : (res >= 11)%nat.

    Ltac split_IH :=
      match goal with
        | [ IH : forall pre : settings * state -> _, _ |- _ ] =>
          (generalize (fun a b => proj1 (IH a b));
            generalize (fun a b => proj2 (IH a b)))
          || (generalize (fun a b c => proj1 (IH a b c));
            generalize (fun a b c => proj2 (IH a b c))); clear IH; intros
        | [ H : forall start len : string, _ |- _ ] =>
          generalize (fun start len H' => H start len (or_introl _ H'));
            specialize (fun start len H' => H start len (or_intror _ H')); intro
        | [ H : forall (data : string) (sch : schema), _ |- _ ] =>
          generalize (fun start len H' => H start len (or_introl _ H'));
            specialize (fun start len H' => H start len (or_intror _ H')); intro
      end.

    Lemma OutList_correct : forall cdatas, cdatasGood cdatas
      -> forall xms,
        List.Forall
        (fun xm => forall avs ts pre im mn (H : importsGlobal im),
          "array8"!"copy" ~~ im ~~> copyS
          -> "array8"!"equal" ~~ im ~~> equalS
          -> wf ns cdatas avs ts xm
          -> (forall start len, freeVar xm (start, len) -> In (start, len) cdatas)
          -> (forall start len, freeVar xm (start, len) -> In start ns /\ In len ns)
          -> (forall specs st, interp specs (pre st)
            -> interp specs (invar cdatas avs ts true (fun x => x) ns res st))
          -> (forall rw data, bindsRowVar xm (rw, data) -> In rw ns /\ In data ns)
          -> goodCursors avs
          -> twfs ts
          -> NoDups avs ts
          -> (forall a V V',
            (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp" -> x <> "matched" ->
              x <> "res" -> x <> "ipos" -> x <> "ilen" -> x <> "ibuf" ->
              (forall rw data, bindsRowVar xm (rw, data) -> x <> rw /\ x <> data)
              -> sel V x = sel V' x) -> invPre a V ===> invPre a V')
          -> (forall a V V' R,
            (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp" -> x <> "matched" ->
              x <> "res" -> x <> "ipos" -> x <> "ilen" -> x <> "ibuf" ->
              (forall rw data, bindsRowVar xm (rw, data) -> x <> rw /\ x <> data)
              -> sel V x = sel V' x) -> invPost a V R = invPost a V' R)
          -> (forall specs st,
            interp specs (Postcondition (toCmd (Out' cdatas avs ts xm) mn H ns res pre) st)
            -> interp specs (invar cdatas avs ts true (fun x => x) ns res st))
          /\ vcs (VerifCond (toCmd (Out' cdatas avs ts xm) mn H ns res pre))) xms
        -> forall avs ts, ForallR (wf ns cdatas avs ts) xms
        -> forall pre im mn (H : importsGlobal im),
          "array8"!"copy" ~~ im ~~> copyS
          -> "array8"!"equal" ~~ im ~~> equalS
          -> (forall start len, ExistsR (fun xm => freeVar xm (start, len)) xms -> In (start, len) cdatas)
          -> (forall start len, ExistsR (fun xm => freeVar xm (start, len)) xms -> In start ns /\ In len ns)
          -> (forall specs st, interp specs (pre st)
            -> interp specs (invar cdatas avs ts true (fun x => x) ns res st))
          -> (forall rw data, ExistsR (fun xm => bindsRowVar xm (rw, data)) xms -> In rw ns /\ In data ns)
          -> goodCursors avs
          -> twfs ts
          -> NoDups avs ts
          -> (forall a V V',
            (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp" -> x <> "matched" ->
              x <> "res" -> x <> "ipos" -> x <> "ilen" -> x <> "ibuf" ->
              (forall rw data, ExistsR (fun xm => bindsRowVar xm (rw, data)) xms -> x <> rw /\ x <> data)
              -> sel V x = sel V' x) -> invPre a V ===> invPre a V')
          -> (forall a V V' R,
            (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp" -> x <> "matched" ->
              x <> "res" -> x <> "ipos" -> x <> "ilen" -> x <> "ibuf" ->
              (forall rw data, ExistsR (fun xm => bindsRowVar xm (rw, data)) xms -> x <> rw /\ x <> data)
              -> sel V x = sel V' x) -> invPost a V R = invPost a V' R)
          -> (forall specs st, interp specs (Postcondition (toCmd (OutList (Out' cdatas avs ts ) xms) mn H ns res pre) st)
            -> interp specs (invar cdatas avs ts true (fun x => x) ns res st))
          /\ vcs (VerifCond (toCmd (OutList (Out' cdatas avs ts) xms) mn H ns res pre)).
      induction 2; simpl; intuition auto 1; split; intros; try apply vcs_app_fwd;
        repeat match goal with
                 | [ H : _ |- vcs _ ] => eapply H; eauto; intros
                 | [ H : _ |- _ ] => eapply H; [ .. | eassumption ]; eauto; intros
               end.
    Qed.

    Hint Extern 1 (goodSize _) => eapply goodSize_weaken; [ eassumption | omega ].

    Lemma inBounds_weaken : forall cdatas V V',
      cdatasGood cdatas
      -> inBounds cdatas V
      -> (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp" -> x <> "matched"
        -> x <> "res" -> sel V x = sel V' x)
      -> inBounds cdatas V'.
      intros; rewrite <- inBounds_sel in *;
        eapply Forall_impl2; [ match goal with
                                 | [ H : cdatasGood _ |- _ ] => apply H
                               end
          | match goal with
              | [ H : inBounds _ _ |- _ ] => apply H
            end
          | ]; cbv beta; intuition idtac;
        match goal with
          | [ H : forall x : string, _ |- _ ] => repeat rewrite <- H by congruence; assumption
        end.
    Qed.

    Hint Extern 1 (inBounds _ _) => eapply inBounds_weaken; [ eassumption | eassumption
      | descend ].

    Ltac deDouble :=
      repeat match goal with
               | [ H : forall start len : string, _ |- _ ] =>
                   specialize (H _ _ eq_refl)
               | [ H : forall (data' : string) (sch' : schema), _ |- _ ] =>
                   specialize (H _ _ eq_refl)
               | [ H : forall rw data : string, _ \/ _ -> _ |- _ ] =>
                 generalize (H _ _ (or_introl _ eq_refl));
                   specialize (fun x y H' => H x y (or_intror _ H')); intuition idtac
             end.

    Ltac clear_fancier :=
      repeat match goal with
               | [ H : importsGlobal _ |- _ ] => clear dependent H
               | [ H : wf _ _ _ _ _ |- _ ] => clear H
               | [ H : ForallR _ _ |- _ ] => clear H
               | [ H : List.Forall _ _ |- _ ] => clear H
             end; clear_fancy.

    Ltac proveHimp :=
      simpl; repeat match goal with
                      | [ V : vals |- _ ] =>
                        progress repeat match goal with
                                          | [ |- context[V ?x] ] => change (V x) with (sel V x)
                                        end
                    end;
      try match goal with
            | [ H : forall x : string, _ |- _ ] => repeat rewrite H by congruence
          end;
      try match goal with
            | [ H : context[invPost] |- context[?P = ?Q] ] =>
              match P with
                | context[invPost ?a ?V ?r] =>
                  match Q with
                    | context[invPost a ?V' r] =>
                      rewrite (H a V V') by intuition
                  end
              end
          end; reflexivity || clear_fancier; sepLemma; eauto; apply himp_star_frame; eauto.

    Lemma convert : forall a b c : W,
      a < b ^- c
      -> c <= b
      -> c ^+ a <= b.
      clear; intros.
      pre_nomega.
      rewrite wordToNat_wplus in *.
      omega.
      apply goodSize_weaken with (wordToNat b); eauto.
    Qed.

    Hint Immediate convert.

    Hint Extern 1 (himp _ _ _) =>
      apply himp_star_frame; try reflexivity; [].

    Hint Extern 1 (himp _ (invPre _ _) (invPre _ _)) =>
      match goal with
        | [ H : _ |- _ ] => apply H; solve [ descend; auto 1 ]
      end.

    Hint Extern 1 (invPre _ _ ===> invPre _ _) =>
      match goal with
        | [ H : _ |- _ ] => apply H; solve [ descend; auto 1 ]
      end.

    Hint Extern 1 (himp _ (invPost ?a ?b ?c) (invPost ?a ?b' ?c)) =>
      match goal with
        | [ HinvPost : context[invPost] |- _ ] =>
          rewrite (HinvPost a b b' c) by descend; reflexivity
      end.

    Lemma convert' : forall (a b c : W) n,
      a < b ^- c
      -> c <= b
      -> n = wordToNat b
      -> (wordToNat c + wordToNat a <= n)%nat.
      clear; intros; subst.
      pre_nomega.
      omega.
    Qed.

    Hint Immediate convert'.

    Ltac vcgen_simp :=
      cbv beta iota zeta
        delta [map app imps Entry Blocks Postcondition VerifCond
          Straightline_ Seq_ Diverge_ Fail_ Skip_ Assert_ Structured.If_
          Structured.While_ Goto_ Structured.Call_ IGoto setArgs Reserved
          Formals Precondition importsMap fullImports buildLocals blocks union
          N.add N.succ Datatypes.length N.of_nat fold_left ascii_lt string_lt
          label'_lt LabelKey.compare' LabelKey.compare LabelKey.eq_dec
          toCmd Seq Instr Diverge Fail Skip Assert_ If_ While_
          Goto Call_ RvImm' Assign' localsInvariant localsInvariantCont regInL
          lvalIn immInR labelIn string_eq ascii_eq andb Bool.eqb
          qspecOut ICall_ Structured.ICall_ Assert_ Structured.Assert_
          string_dec Ascii.ascii_dec string_rec string_rect
          sumbool_rec sumbool_rect Ascii.ascii_rec Ascii.ascii_rect
          Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym fst
          snd Ascii.N_of_ascii Ascii.N_of_digits N.compare N.mul
          Pos.compare Pos.compare_cont Pos.mul Pos.add
          Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec
          ZArith_dec.Z_gt_le_dec Int.Z_as_Int.plus Int.Z_as_Int.max
          ZArith_dec.Z_gt_dec Int.Z_as_Int._1 BinInt.Z.add
          Int.Z_as_Int._0 Int.Z_as_Int._2 BinInt.Z.max ZArith_dec.Zcompare_rec
          ZArith_dec.Z_ge_lt_dec BinInt.Z.compare ZArith_dec.Zcompare_rect
          ZArith_dec.Z_ge_dec label'_eq label'_rec label'_rect COperand1 CTest
          COperand2 Pos.succ makeVcs Note_ Note__ IGotoStar_ IGotoStar
          AssertStar_ AssertStar Cond_ Cond
          Wrap WrapC SimpleSeq StringWrite clarify];
        my_refold.

    Ltac step1 :=
      match goal with
        | [ |- context[Select] ] =>
          simpl; propxFo; erewrite findTable_good in * by eauto;
            deDouble; intuition subst;
              try match goal with
                    | [ |- vcs _ ] => wrap0
                  end; eauto;
              try match goal with
                    | [ IH : _ |- vcs _ ] =>
                      eapply IH; clear IH; eauto
                    | [ IH : _, H : interp _ (Postcondition _ _) |- _ ] =>
                      apply IH in H; clear IH; eauto
                  end
        | [ |- context[Column] ] =>
          simpl; intros;
            match goal with
              | [ H : Logic.ex _ |- _ ] => destruct H as [ ? [ ? [ ] ] ]
            end; erewrite findCursor_good by eauto; vcgen_simp;
            post; try match goal with
                        | [ |- vcs (_ :: _) ] => wrap0; try discriminate
                      end
        | [ |- context[IfEqual] ] =>
          simpl; propxFo;
            do 2 erewrite findCursor_good in * by eauto;
              try match goal with
                    | [ H : interp _ _ |- _ ] =>
                      generalize dependent H; vcgen_simp; propxFo
                  end;
              match goal with
                | [ |- vcs _ ] =>
                  vcgen_simp; wrap0;
                  try match goal with
                        | [ |- vcs _] => fold (@app Prop); wrap0;
                          rewrite toCmd'_eq; match goal with
                                               | [ IH : _ |- _ ] => apply IH; eauto
                                             end
                      end
                | _ => deDouble; intuition subst;
                  match goal with
                    | [ H : interp _ _, IH : _ |- _ ] =>
                      rewrite toCmd'_eq in H;
                        apply IH in H; eauto; [ | clear H ]; (deSpec; t)
                  end
                | _ => idtac
              end
        | _ =>
          intros; split; unfold Out'; match goal with
                                        | [ |- context[OutList] ] => simpl
                                        | _ => vcgen_simp
                                      end;
            post; try match goal with
                        | [ |- vcs (_ :: _) ] => wrap0; try discriminate
                      end;
            try match goal with
                  | _ => apply OutList_correct; auto
                  | [ H : _ |- _ ] => apply OutList_correct in H; auto
                end
      end.

    Ltac step2 := abstract (deDouble; deSpec; intuition subst;
      solve [ t | proveHimp ]).

    Lemma cursor_survived : forall tab t avs,
      In t avs
      -> tab <> Name (Table t)
      -> In t (removeCursor tab avs).
      clear; induction avs; simpl; intuition;
        ift; simpl; intuition.
    Qed.

    Hint Immediate cursor_survived.

    Lemma NoDup_survived' : forall tab' tab avs,
      In tab' (ANames (removeCursor tab avs))
      -> In tab' (ANames avs).
      clear; induction avs; simpl; intuition;
        generalize dependent H; ift; simpl in *; intuition.
    Qed.

    Lemma NoDup_survived : forall tab avs,
      NoDup (ANames avs)
      -> NoDup (ANames (removeCursor tab avs)).
      clear; induction avs; inversion_clear 1; simpl; intuition.
      ift; simpl; intuition eauto using NoDup_survived'.
    Qed.

    Hint Resolve NoDup_survived.

    Lemma double_cursor_appear : forall V avs av1 av2 P,
      In av1 avs
      -> In av2 avs
      -> Name (Table av1) <> Name (Table av2)
      -> NoDup (ANames avs)
      -> cursors V avs * P
      ===> P * (cursor V av1 * (cursor V av2
        * cursors V (removeCursor (Name (Table av2))
          (removeCursor (Name (Table av1)) avs)))).
      clear; sepLemma.
      etransitivity; [ apply release_cursor; try apply H; eauto | ]; sepLemma.
      etransitivity; [ apply release_cursor; eauto | ]; sepLemma.
    Qed.

    Hint Extern 1 (himp _ _ _) => apply double_cursor_appear.

    Lemma goodSize_goodCursors : forall t avs,
      In t avs
      -> goodCursors avs
      -> goodSize (length (Schema (Table t))).
      clear; intros.
      eapply Forall_forall in H0; [ | eassumption ].
      tauto.
    Qed.

    Hint Immediate goodSize_goodCursors.

    Lemma sel_upd_Data : forall av x vs v,
      (exists avs, goodCursors avs /\ In av avs)
      -> In x cvars
      -> sel (upd vs x v) (Data av) = sel vs (Data av).
      clear; destruct 1; intros; apply sel_upd_ne; intuition.
      eapply Forall_forall in H2; eauto; intuition.
    Qed.

    Lemma sel_upd_Row : forall av x vs v,
      (exists avs, goodCursors avs /\ In av avs)
      -> In x cvars
      -> sel (upd vs x v) (Row av) = sel vs (Row av).
      clear; destruct 1; intros; apply sel_upd_ne; intuition.
      eapply Forall_forall in H2; eauto; intuition.
    Qed.

    Hint Rewrite sel_upd_Data sel_upd_Row
      using ((simpl; tauto) || (do 2 esplit; eassumption)) : sepFormula.

    Lemma Out_correct : forall cdatas, cdatasGood cdatas
      -> incl baseVars ns
      -> forall xm avs ts pre im mn (H : importsGlobal im),
        "array8"!"copy" ~~ im ~~> copyS
        -> "array8"!"equal" ~~ im ~~> equalS
        -> wf ns cdatas avs ts xm
        -> (forall start len, freeVar xm (start, len) -> In (start, len) cdatas)
        -> (forall start len, freeVar xm (start, len) -> In start ns /\ In len ns)
        -> (forall specs st, interp specs (pre st)
          -> interp specs (invar cdatas avs ts true (fun x => x) ns res st))
        -> (forall rw data, bindsRowVar xm (rw, data) -> In rw ns /\ In data ns)
        -> goodCursors avs
        -> twfs ts
        -> NoDups avs ts
        -> (forall a V V', (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp"
            -> x <> "matched" -> x <> "res"
            -> x <> "ipos" -> x <> "ilen" -> x <> "ibuf"
            -> (forall rw data, bindsRowVar xm (rw, data) -> x <> rw /\ x <> data)
            -> sel V x = sel V' x)
          -> invPre a V ===> invPre a V')
        -> (forall a V V' R, (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp"
            -> x <> "matched" -> x <> "res"
            -> x <> "ipos" -> x <> "ilen" -> x <> "ibuf"
            -> (forall rw data, bindsRowVar xm (rw, data) -> x <> rw /\ x <> data)
            -> sel V x = sel V' x)
          -> invPost a V R = invPost a V' R)
        -> (forall specs st, interp specs (Postcondition (toCmd (Out' cdatas avs ts xm) mn H ns res pre) st)
          -> interp specs (invar cdatas avs ts true (fun x => x) ns res st))
        /\ vcs (VerifCond (toCmd (Out' cdatas avs ts xm) mn H ns res pre)).
      induction xm using xml_ind'.

      step1.

      step2.
      step2.
      step2.
      step2.

      step1.

      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.

      step1.

      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.

      step1.

      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.

      step1.

      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.

      step1.

      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
    Qed.
  End Out_correct.

  Notation OutVcs cdatas avs ts xm := (fun im ns res =>
    (~In "rp" ns) :: In "obuf" ns :: In "olen" ns :: In "opos" ns :: In "overflowed" ns
    :: In "tmp" ns :: In "buf" ns :: In "matched" ns :: In "res" ns
    :: (forall a V V', (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp"
      -> x <> "matched" -> x <> "res"
      -> x <> "ipos" -> x <> "ilen" -> x <> "ibuf"
      -> (forall rw data, bindsRowVar xm (rw, data) -> x <> rw /\ x <> data)
      -> sel V x = sel V' x)
    -> invPre a V ===> invPre a V')
    :: (forall a V V' R, (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp"
      -> x <> "matched" -> x <> "res"
      -> x <> "ipos" -> x <> "ilen" -> x <> "ibuf"
      -> (forall rw data, bindsRowVar xm (rw, data) -> x <> rw /\ x <> data)
      -> sel V x = sel V' x)
    -> invPost a V R = invPost a V' R)
    :: (res >= 11)%nat
    :: wf ns cdatas avs ts xm
    :: (forall start len, freeVar xm (start, len) -> In (start, len) cdatas)
    :: (forall start len, freeVar xm (start, len) -> In start ns /\ In len ns)
    :: cdatasGood cdatas
    :: "array8"!"copy" ~~ im ~~> copyS
    :: "array8"!"equal" ~~ im ~~> equalS
    :: incl baseVars ns
    :: (forall rw data, bindsRowVar xm (rw, data) -> In rw ns /\ In data ns)
    :: goodCursors avs
    :: twfs ts%list
    :: NoDups avs ts%list
    :: nil).

  Definition Out (cdatas : list (string * string)) (avs : list avail) (ts : tables) (xm : xml) : chunk.
    refine (WrapC (Out' cdatas avs ts xm)
      (invar cdatas avs ts)
      (invar cdatas avs ts)
      (OutVcs cdatas avs ts xm)
      _ _); abstract (intros; repeat match goal with
                                       | [ H : vcs (_ :: _) |- _ ] => inversion_clear H; subst
                                     end; eapply Out_correct; eauto).
  Defined.
End Out.
