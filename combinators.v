Set Implicit Arguments.
Generalizable All Variables.
Set Universe Polymorphism.
Set Asymmetric Patterns.
(*
Section helper.
(* Fixpoint foldl A B (f : A -> B -> A) (x0 : A) (l : list B) : A :=
    match l with
      | nil => x0
      | cons x xs => foldl f (f x0 x) xs
    end.

  Fixpoint foldr A B (f : A -> B -> B) (x0 : B) (l : list A) : B :=
    match l with
      | nil => x0
      | cons x xs => f x (foldr f x0 xs)
    end.

  Inductive listElem T : list T -> Type :=
  | First : forall x xs, listElem (x::xs)
  | Next : forall x xs, listElem xs -> listElem (x::xs).

  Fixpoint listElemDenote T (l : list T) (e : listElem l) :=
    match e with
      | First x xs => x
      | Next x xs e' => listElemDenote e'
    end.*)
End helper.*)

Section function_spec.
  (** We reify the type of arrows, so that we can reason about them.
      We include a special value, the type of the class on which this
      is defined. *)

  Inductive FunctionType : Type :=
  | const_class_type : FunctionType
  | const : Type -> FunctionType
  | arrow : FunctionType -> FunctionType -> FunctionType.

  Fixpoint FunctionTypeDenote (class_type : Type) (T : FunctionType) :=
    match T with
      | const_class_type => class_type
      | const T' => T'
      | arrow L R => (FunctionTypeDenote class_type L) -> (FunctionTypeDenote class_type R)
    end.

  Fixpoint Function_coerce A_class B_class (f : A_class -> B_class) (g : B_class -> A_class)
           T
  : FunctionTypeDenote A_class T -> FunctionTypeDenote B_class T
    := match T with
         | const_class_type => f
         | const T' => fun x => x
         | arrow L R => fun F x
                        => let x' := @Function_coerce B_class A_class g f L x in
                           @Function_coerce A_class B_class f g R (F x')
       end.

  (** We will eventually need to talk about functions which spit out a class type, and which take in a class type. *)
  Inductive variance := variance_in | variance_out.
  Definition variance_op (v : variance) := match v with variance_in => variance_out | variance_out => variance_in end.

  (** [function_type_only_in] specifies that a given [FunctionType] never needs to construct a [class_type], only look at them *)
  Inductive function_type_only_one_way : variance -> FunctionType -> Type :=
  (** constant types are fine; we don't need to construct a class type *)
  | const_only_in : forall T, function_type_only_one_way variance_in (const T)
  (** if the left side only constructs class types and the right side only looks at class types, then we're fine *)
  | arrow_only_in : forall L R,
                      function_type_only_one_way variance_out L
                      -> function_type_only_one_way variance_in R
                      -> function_type_only_one_way variance_in (arrow L R)
  | const_only_out : forall T, function_type_only_one_way variance_out (const T)
  | class_only_out : function_type_only_one_way variance_out const_class_type
  | arrow_only_out : forall L R,
                      function_type_only_one_way variance_in L
                      -> function_type_only_one_way variance_out R
                      -> function_type_only_one_way variance_out (arrow L R).

  (** We can coerce from only_out functions on A to functions on B with only a function [f : A -> B], and vice-versa. *)
  Fixpoint Function_only_one_way_coerce A_class B_class (f : A_class -> B_class)
           T
           {v : variance}
           (H : function_type_only_one_way v T)
  : FunctionTypeDenote (match v with variance_out => A_class | variance_in => B_class end) T
    -> FunctionTypeDenote (match v with variance_out => B_class | variance_in => A_class end) T
    := match H in (function_type_only_one_way v T)
             return FunctionTypeDenote (match v with variance_out => A_class | variance_in => B_class end) T
                    -> FunctionTypeDenote (match v with variance_out => B_class | variance_in => A_class end) T
       with
         | const_only_out T' => fun x => x
         | class_only_out => f
         | arrow_only_out L R L_in R_out
           => fun F x
              => let x' := @Function_only_one_way_coerce A_class B_class f L _ L_in x in
                 @Function_only_one_way_coerce A_class B_class f R _ R_out (F x')
         | const_only_in T' => fun x => x
         | arrow_only_in L R L_out R_in
           => fun F x
              => let x' := @Function_only_one_way_coerce A_class B_class f L _ L_out x in
                 @Function_only_one_way_coerce A_class B_class f R _ R_in (F x')
       end.


  (** We can also coerce functions with different specs, if we have
      the right intermediate functions.  We assume we only have a
      function [A -> B], not [B -> A] *)

  Inductive function_types_compatible
  : forall (A B : FunctionType) (v : variance),
      Type
    :=
    | compatible_const_out : forall T_A T_B (f : T_A -> T_B),
                                 function_types_compatible (const T_A) (const T_B) variance_out
    | compatible_const_in : forall T_A T_B (f0 : T_B -> T_A),
                              function_types_compatible (const T_A) (const T_B) variance_in
    | compatible_class_out : function_types_compatible const_class_type const_class_type variance_out
    | compatible_arrow : forall v L_A R_A L_B R_B,
                               function_types_compatible L_A L_B (variance_op v)
                               -> function_types_compatible R_A R_B v
                               -> function_types_compatible (arrow L_A R_A) (arrow L_B R_B) v.

  (** If two function types are compatible, we can coerce from one to
      the other, given an isomorphism of the internal models.

      TODO: Really, we should require that it's an
      equivalence/isomorphism, but, for now, we just require a
      function in each direction. *)

  Fixpoint function_types_compatible_coerce A_spec B_spec
           A_class B_class
           {v : variance}
           (f : A_class -> B_class)
           (H : function_types_compatible A_spec B_spec v)
  : match v with
      | variance_out => FunctionTypeDenote A_class A_spec
      | variance_in => FunctionTypeDenote B_class B_spec
    end
    -> match v with
         | variance_out => FunctionTypeDenote B_class B_spec
         | variance_in => FunctionTypeDenote A_class A_spec
       end
    := match
        H in (function_types_compatible A_spec B_spec v)
        return
        (match v with
           | variance_out => FunctionTypeDenote A_class A_spec
           | variance_in => FunctionTypeDenote B_class B_spec
         end
         -> match v with
              | variance_out => FunctionTypeDenote B_class B_spec
              | variance_in => FunctionTypeDenote A_class A_spec
            end)
      with
        | @compatible_const_out T_A T_B f0 => f0
        | @compatible_const_in T_A T_B f0 => f0
        | compatible_class_out => f
        | @compatible_arrow variance_out L_A R_A L_B R_B H0 H1
          => fun F x
             => let x' := @function_types_compatible_coerce _ _ _ _ _ f H0 x in
                @function_types_compatible_coerce _ _ _ _ _ f H1 (F x')
        | @compatible_arrow variance_in L_A R_A L_B R_B H0 H1
          => fun F x
             => let x' := @function_types_compatible_coerce _ _ _ _ _ f H0 x in
                @function_types_compatible_coerce _ _ _ _ _ f H1 (F x')
      end.



  (** An abstract data type spec has a type of function names, and for
      each function name, a type signature for that function. *)

  Record ADTSpec :=
    {
      ADTFunctionNames : Type;
      ADTFunctionSpec : ADTFunctionNames -> FunctionType
    }.

  (** An abstract data type implementation, which implements the
      interface [S], has an internal representation ([ADTModel]),
      which is passed as the [class_type] parameter to
      [FunctionTypeDenote], and an implementation of each specified
      function. *)

  Record ADTImplementation (S : ADTSpec) :=
    {
      ADTModel :> Type;
      ADTFunctions : forall e, FunctionTypeDenote ADTModel (ADTFunctionSpec S e)
    }.
(*
  (** To implement the product combinator, we require that all
      mutation functions match in type signatures.  A specification
      [f] specifies a mutation function if, when fully
      denoted on a class type [T] and fully applied, the return type is [T]. *)
  Fixpoint is_mutation_spec (f : FunctionType) : bool :=
    match f with
      | const_class_type => true
      | arrow _ R => is_mutation_spec R
      | _ => false
    end.
*)
  (** A skeleton for a product of two [ADTSpec]s [A] and [B] consists
      of a type [T] of function names, and a map [T ->
      (ADTFunctionNames A) + (ADTFunctionNames B) + (ADTFunctionNames
      A * ADTFunctionNames B)] which maps each name to a call of
      either a function of [A], a function of [B], or a function of
      [A] and also a function of [B], together with a proof that the
      function specs match up.  If we only have one function, then we
      require that the function doesn't need to produce any product
      ADTs

      We require that when you give a pair of specs, they both are
      "only out" kind of specs, or they line up perfectly and not only
      up to function existance on the non-"only out" parts; a product
      is a terminal object. *)

  (** We actually require a fresh function type and means of
      generating that function from the [A] and [B] types.  This can
      later be automated to work nicely if the types line up
      appropriately. *)
(*
  Inductive function_types_compatible
  : forall (A B : FunctionType),
      Type
    :=
    | compatible_const : forall T_A T_B (f : T_A -> T_B),
                                 function_types_compatible (const T_A) (const T_B)
    | compatible_class : function_types_compatible const_class_type const_class_type
    | compatible_arrow : forall L_A R_A L_B R_B,
                           function_types_compatible L_B L_A
                           -> function_types_compatible R_A R_B
                           -> function_types_compatible (arrow L_A R_A) (arrow L_B R_B).


  (** If two function types are compatible, we can coerce from one to
      the other, given an isomorphism of the internal models.

      TODO: Really, we should require that it's an
      equivalence/isomorphism, but, for now, we just require a
      function in each direction. *)

  Fixpoint function_types_compatible_coerce A_spec B_spec
           A_class B_class
           (f : A_class -> B_class)
           (g : B_class -> A_class)
           (H : function_types_compatible A_spec B_spec)
  : FunctionTypeDenote A_class A_spec -> FunctionTypeDenote B_class B_spec
    := match
        H in (function_types_compatible from to)
        return
        (FunctionTypeDenote A_class from -> FunctionTypeDenote B_class to)
      with
        | @compatible_const T_A T_B f0 => f0
        | compatible_class => f
        | @compatible_arrow L_A R_A L_B R_B H0 H1
          => fun F x
             => let x' := @function_types_compatible_coerce _ _ B_class A_class g f H0 x in
                @function_types_compatible_coerce _ _ A_class B_class f g H1 (F x')
      end.
*)


  Inductive function_types_compatible_for_prod
  : forall (A B AB : FunctionType) (v : variance),
      Type
    :=
    | prod_compatible_const_out : forall T_A T_B T_AB (f : T_A * T_B -> T_AB),
                                 function_types_compatible_for_prod (const T_A) (const T_B) (const T_AB) variance_out
    | prod_compatible_const_in : forall T_A T_B T_AB (f0 : T_AB -> T_A * T_B),
                                 function_types_compatible_for_prod (const T_A) (const T_B) (const T_AB) variance_in
    | prod_compatible_class : forall v, function_types_compatible_for_prod const_class_type const_class_type const_class_type v
    | prod_compatible_arrow_out : forall L_A R_A L_B R_B L_AB R_AB,
                                    function_types_compatible_for_prod L_A L_B L_AB variance_in
                                    -> function_types_compatible_for_prod R_A R_B R_AB variance_out
                                    -> function_types_compatible_for_prod (arrow L_A R_A) (arrow L_B R_B) (arrow L_AB R_AB) variance_out
    | prod_compatible_arrow_in : forall L_A R_A L_B R_B L_AB R_AB,
                                   function_types_compatible L_AB L_A variance_in
                                   -> function_types_compatible L_AB L_B variance_in
                                   -> function_types_compatible_for_prod R_A R_B R_AB variance_in
                                   -> function_types_compatible_for_prod (arrow L_A R_A) (arrow L_B R_B) (arrow L_AB R_AB) variance_in.

  (** If two function types are compatible, we can coerce from one to
      the other, given an isomorphism of the internal models.

      TODO: Really, we should require that it's an
      equivalence/isomorphism, but, for now, we just require a
      function in each direction. *)

  Fixpoint function_types_compatible_coerce_prod A_spec B_spec AB_spec
           A_class B_class AB_class
           (cpair : A_class -> B_class -> AB_class)
           (cfst : AB_class -> A_class)
           (csnd : AB_class -> B_class)
           {v}
           (H : function_types_compatible_for_prod A_spec B_spec AB_spec v)
  : match v with
      | variance_out => FunctionTypeDenote A_class A_spec * FunctionTypeDenote B_class B_spec
      | variance_in => FunctionTypeDenote AB_class AB_spec
    end
    -> match v with
         | variance_out => FunctionTypeDenote AB_class AB_spec
         | variance_in => FunctionTypeDenote A_class A_spec * FunctionTypeDenote B_class B_spec
       end
    := match
        H in (function_types_compatible_for_prod A_spec B_spec AB_spec v)
        return
        (match v with
           | variance_out => FunctionTypeDenote A_class A_spec * FunctionTypeDenote B_class B_spec
           | variance_in => FunctionTypeDenote AB_class AB_spec
         end
         -> match v with
              | variance_out => FunctionTypeDenote AB_class AB_spec
              | variance_in => FunctionTypeDenote A_class A_spec * FunctionTypeDenote B_class B_spec
            end)
      with
        | @prod_compatible_const_out T_A T_B T_AB f0 => f0
        | @prod_compatible_const_in T_A T_B T_AB f0 => f0
        | @prod_compatible_class variance_out => fun ab => cpair (fst ab) (snd ab)
        | @prod_compatible_class variance_in => fun ab => (cfst ab, csnd ab)
        | @prod_compatible_arrow_out L_A R_A L_B R_B L_AB R_AB H0 H1
          => fun F x
             => let x' := @function_types_compatible_coerce_prod _ _ _ _ _ _ cpair cfst csnd _ H0 x in
                @function_types_compatible_coerce_prod _ _ _ _ _ _ cpair cfst csnd _ H1 ((fst F) (fst x'),
                                                                                         (snd F) (snd x'))
        | @prod_compatible_arrow_in L_A R_A L_B R_B L_AB R_AB H0 H1 H2
          => fun F
             => ((fun x => let x' := @function_types_compatible_coerce _ _ _ _ _ cfst H0 x in
                           fst (@function_types_compatible_coerce_prod _ _ _ _ _ _ cpair cfst csnd _ H2 (F x'))),
                 (fun x => let x' := @function_types_compatible_coerce _ _ _ _ _ csnd H1 x in
                           snd (@function_types_compatible_coerce_prod _ _ _ _ _ _ cpair cfst csnd _ H2 (F x'))))
      end.

  Record ADTSpecProductSkeleton (A B : ADTSpec) :=
    {
      ADTPFunctionNames : Type;
      ADTPFunctionMap : ADTPFunctionNames
                        -> { a : ADTFunctionNames A & function_type_only_one_way variance_in (ADTFunctionSpec A a) }
                           + { b : ADTFunctionNames B & function_type_only_one_way variance_in (ADTFunctionSpec B b) }
                           + { ab : ADTFunctionNames A * ADTFunctionNames B
                             & { ab_type : FunctionType
                               & (function_types_compatible_for_prod (ADTFunctionSpec A (fst ab))
                                                                     (ADTFunctionSpec B (snd ab))
                                                                     ab_type
                                                                     variance_out) } }
    }.

  Section prod.
    Variables A_spec B_spec : ADTSpec.

    Variable AB_spec_skeleton : ADTSpecProductSkeleton A_spec B_spec.

    Definition ADTProductSpec : ADTSpec
      := {| ADTFunctionNames := ADTPFunctionNames AB_spec_skeleton;
            ADTFunctionSpec name := match ADTPFunctionMap AB_spec_skeleton name with
                                      | inl (inl f) => ADTFunctionSpec A_spec (projT1 f)
                                      | inl (inr f) => ADTFunctionSpec B_spec (projT1 f)
                                      | inr abh => projT1 (projT2 abh)
                                    end |}.

    Definition ADTProduct (A : ADTImplementation A_spec) (B : ADTImplementation B_spec)
    : ADTImplementation ADTProductSpec
      := Build_ADTImplementation
           ADTProductSpec
           (ADTModel A * ADTModel B)
           (fun name => match ADTPFunctionMap AB_spec_skeleton name as fname
                              return FunctionTypeDenote
                                       (ADTModel A * ADTModel B)
                                       (match fname with
                                          | inl (inl f) => ADTFunctionSpec A_spec (projT1 f)
                                          | inl (inr f) => ADTFunctionSpec B_spec (projT1 f)
                                          | inr abh => projT1 (projT2 abh)
                                        end)
                        with
                          | inl (inl f) => Function_only_one_way_coerce (@fst A B) (projT2 f) (ADTFunctions A (projT1 f))
                          | inl (inr f) => Function_only_one_way_coerce (@snd A B) (projT2 f) (ADTFunctions B (projT1 f))
                          | inr abh => function_types_compatible_coerce_prod
                                         (@pair A B) (@fst A B) (@snd A B)
                                         (projT2 (projT2 abh))
                                         (ADTFunctions A (fst (projT1 abh)),
                                          ADTFunctions B (snd (projT1 abh)))
                        end).
  End prod.
End function_spec.
