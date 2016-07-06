Require Export
        Fiat.CertifiedExtraction.Extraction.Extraction.

Require Import
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Basics
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Wrappers
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Properties.

Require Import
        Coq.Program.Program
        Coq.Lists.List.

Unset Implicit Arguments.

Lemma CompileCompose :
  forall {av} E B B' (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B') (stream: B) (cache: E)
    (tenv t1 t2: Telescope av) f (g: B -> B') ext env p1 p2,
    (forall a1 a2 b, f (a1, b) = f (a2, b)) ->
    {{ [[ vstream  ->> g stream as _ ]]
         :: tenv }}
      p1
    {{ TelAppend ([[ NTNone ->> enc1 cache as encoded1 ]]
                    :: [[ vstream ->> g (Transformer.transform stream (fst encoded1)) as _ ]]
                    :: f encoded1)
                 t1 }}
    ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform stream (fst encoded1) in
     {{ TelAppend ([[ vstream ->> g stream1 as _ ]] :: f encoded1) t1 }}
       p2
     {{ TelAppend ([[ NTNone ->> enc2 (snd encoded1) as encoded2 ]]
                     :: [[ vstream ->> g (Transformer.transform stream1 (fst encoded2)) as _ ]]
                     :: f encoded2) t2 }}
     ∪ {{ ext }} // env) ->
    {{ [[ vstream ->> g stream as _ ]] :: tenv }}
      (Seq p1 p2)
    {{ TelAppend ([[ NTNone ->> @Compose.compose E B transformer enc1 enc2 cache as composed ]]
                    :: [[ vstream ->> g (Transformer.transform stream (fst composed)) as _ ]]
                    :: f composed) t2 }}
    ∪ {{ ext }} // env.
Proof.
  intros.
  repeat hoare.
  setoid_rewrite Compose_compose_acc.
  unfold compose_acc, encode_continue.
  cbv zeta in *.
  setoid_rewrite Propagate_anonymous_ret.
  setoid_rewrite Propagate_anonymous_ret in H0.
  setoid_rewrite Propagate_anonymous_ret in H1.
  destruct (enc1 _); simpl in *.
  destruct (enc2 _); simpl in *.
  erewrite (H (Transformer.transform _ _)); rewrite Transformer.transform_assoc; eassumption.
Qed.

Lemma CompileCompose_init :
  forall {av} E B B' (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B') (cache: E)
    (tenv t1 t2: Telescope av) f (g : B -> B') ext env p1 p2 pAlloc,
    (forall a1 a2 b, f (a1, b) = f (a2, b)) ->
    {{ tenv }}
      pAlloc
    {{ [[ vstream ->> g Transformer.transform_id as _ ]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[ vstream ->> g Transformer.transform_id as _ ]] :: tenv }}
      p1
    {{ TelAppend ([[ NTNone ->> enc1 cache as encoded1 ]]
                    :: [[ vstream ->> g (Transformer.transform (Transformer.transform_id) (fst encoded1)) as _ ]]
                    :: f encoded1)
                 t1 }} ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform Transformer.transform_id (fst encoded1) in
     {{ TelAppend ([[ vstream ->> g stream1 as _ ]] :: f encoded1) t1 }}
       p2
     {{ TelAppend ([[ NTNone ->> enc2 (snd encoded1) as encoded2 ]]
                     :: [[ vstream ->> g (Transformer.transform stream1 (fst encoded2)) as _ ]]
                     :: f encoded2) t2 }} ∪ {{ ext }} // env) ->
    {{ tenv }}
      (Seq pAlloc (Seq p1 p2))
    {{ TelAppend ([[ NTNone ->> @Compose.compose E B transformer enc1 enc2 cache as composed ]]
                    :: [[ vstream ->> g (fst composed) as _ ]]
                    :: f composed) t2 }}
    ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  setoid_rewrite <- (Transformer.transform_id_left (fst _)).
  eauto using CompileCompose.
Qed.
