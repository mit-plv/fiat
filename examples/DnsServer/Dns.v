Require Import AutoDB BagADT.
Require Import Vector Ascii Bool Bvector List.

Definition name := list string.

Inductive type := A | CNAME | NS | MX.
Inductive class := IN | CH | HS.

Record question :=
  { qname : name;
    qtype : type;
    qclass : class }.

Record answer :=
  { aname : name;
    atype : type;
    aclass : class;
    ttl : nat;
    rdata : string }.

Record packet :=
  { id : Bvector 16;
    flags : Bvector 16;
    questions : question; (* `list question` in case we can have multiple questions? *)
    answers : list answer;
    authority : list answer;
    additional : list answer }.

Definition sCOLLECTIONS := "Collections".
Definition sNAME := "Name".
Definition sTTL := "TTL".
Definition sCLASS := "Class".
Definition sTYPE := "Type".
Definition sDATA := "Data".

Definition DnsSchema :=
  Query Structure Schema
        [ relation sCOLLECTIONS has
                   schema <sNAME :: name,
                           sTYPE :: type,
                           sCLASS :: class,
                           sTTL :: nat,
                           sDATA :: string>
          where (fun t t' =>
                   t!sNAME = t'!sNAME -> t!sTYPE <> CNAME /\ t'!sTYPE <> CNAME)]
        enforcing [ ].

Definition DnsTuple := TupleDef DnsSchema sCOLLECTIONS.
Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "AddData" : rep x DnsTuple -> rep x bool,
      Method "Process" : rep x packet -> rep x packet
  }.

Definition beq_string (p s : string) := if string_dec p s then true else false.

Definition prefixProp (p s : name) := exists ps, List.app p ps = s.
Fixpoint prefixBool (p s : name) :=
  match p, s with
    | List.nil, _ => true 
    | List.cons p' ps', List.cons s' ss' => andb (beq_string p' s') (prefixBool ps' ss')
    | _, _ => false
  end.

Definition upperbound (r : DnsTuple) (rs : list DnsTuple) :=
  forall r', List.In r' rs -> List.length r!sNAME >= List.length r'!sNAME.

Lemma zero_lt_sixteen : lt 0 16. omega. Qed.
Definition buildempty (p : packet) :=
  {| id := id p;
     flags := replace_order (flags p) zero_lt_sixteen true; (* set QR bit *)
     questions := questions p;
     answers := List.nil;
     authority := List.nil;
     additional := List.nil |}.

Definition toAnswer (t: DnsTuple) :=
  {| aname := t!sNAME;
     atype := t!sTYPE;
     aclass := t!sCLASS;
     ttl := t!sTTL;
     rdata := t!sDATA |}.

Definition addan (p : packet) (t : DnsTuple) :=
  {| id := id p;
     flags := flags p;
     questions := questions p;
     answers := (toAnswer t) :: answers p;
     authority := authority p;
     additional := additional p |}.

Definition addns (p : packet) (t : DnsTuple) :=
  {| id := id p;
     flags := flags p;
     questions := questions p;
     answers := answers p;
     authority := (toAnswer t) :: (authority p);
     additional := additional p |}.

Fixpoint Fix A R (i : nat) (body : (A -> R) -> A -> R) (base : R) (arg : A) :=
  match i with
    | O => base
    | S i' => body (Fix i' body base) arg
  end.

Add Parametric Morphism A R i
: (@Fix A (Comp R) i)
    with signature
    (fun f g => forall a a' r, (forall b, refine (a b) (a' b)) -> refine (f a r) (g a' r))
      ==> (@refine R) 
      ==> (@eq A)
      ==> (@refine R)
      as refineFix.
Proof.
  simpl; induction i; intros; simpl.
  - assumption.
  - apply H; apply IHi; [ apply H | apply H0 ].
Qed.

Arguments Fix : simpl never.

Notation "'Filter' xs | p" := (Pick (fun xs' => forall x, List.In x xs' <-> List.In x xs /\ p x)) (at level 70) : comp_scope.
Notation "'unique' b , p ->> s 'otherwise' ->> s'" := 
  (Bind (Pick (fun b' => forall b, b' = Some b <-> p)) (fun b' =>
   match b' with
     | Some b => s
     | None => s'
   end)) (at level 70).

Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,
    update "AddData" (t : DnsTuple) : bool :=
      Insert t into sCOLLECTIONS,
    query "Process" (p : packet) : packet :=
      let t := qtype (questions p) in
      Fix 7 (fun (rec : name -> Comp packet) (n : name)  =>
         rs <- For (r in sCOLLECTIONS)
            Where (prefixProp r!sNAME n)
            Return r;
         bfrs <- Filter rs | (fun x : DnsTuple => upperbound x rs);
         b <- { b | decides b (forall r, List.In r bfrs -> n = r!sNAME) };
         if b
         then
           unique b, List.In b bfrs /\ b!sTYPE = CNAME /\ t <> CNAME ->>
             bfrs' <- Filter bfrs | (fun x : DnsTuple => x!sTYPE = t);
             p' <- rec b!sNAME;
             ret (List.fold_left addan bfrs' p')
           otherwise ->>
             ret (List.fold_left addan bfrs (buildempty p))
         else
           bfrs' <- Filter bfrs | (fun x : DnsTuple => x!sTYPE = NS);
           ret (List.fold_left addns bfrs' (buildempty p))
      ) (ret (buildempty p)) (qname (questions p))
  }.

Definition SearchTerm (s : name) (t : DnsSchema # sCOLLECTIONS) :=
  prefixBool (t!sNAME) s.
Definition DnsTerm :=
  {| BagSearchTermType := name;
     BagMatchSearchTerm := SearchTerm;
     BagUpdateTermType := name;
     BagApplyUpdateTerm := fun _ x => x |}.

Theorem DnsManual :
  Sharpened DnsSpec.
Proof.
  unfold DnsSpec.
  start honing QueryStructure.

  hone representation using (@DelegateToBag_AbsR DnsSchema (icons DnsTerm (inil _))).
  
  hone constructor "Init".
  {
    simplify with monad laws.
    rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure.
    finish honing.
  }
  
  hone method "AddData".
  {
    simplify with monad laws.
  }
  
  hone method "Process".
  {
    simplify with monad laws.
    implement_In.
  }

Defined.
  FullySharpenQueryStructure DnsSchema Index.