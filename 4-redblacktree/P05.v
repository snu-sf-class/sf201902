Require Export P04.



(** **** Exercise: 4 stars (balance_relate)  *)
(** You will need proof automation for this one.  Study the methods used
  in [ins_not_E] and [balance_SearchTree], and try them here.
  Add one clause at a time to your [match goal]. *)
Lemma Abs_helper:
  forall m' t m, Abs t m' ->    m' = m ->     Abs t m.
Proof.
   intros. subst. auto.
Qed.

Ltac contents_equivalent_prover :=
 extensionality x; unfold t_update, combine, t_empty;
 repeat match goal with
  | |- context [if ?A then _ else _] => bdestruct A
 end;
 auto;
 omega.

Theorem balance_relate:
  forall c l k vk r m,
    SearchTree (T c l k vk r) ->
    Abs (T c l k vk r) m ->
    Abs (balance c l k vk r) m.
Proof.
intros.
inv H.
unfold balance.
repeat match goal with
 | H: Abs E _ |- _ => inv H
end.
(** Add these clauses, one at a time, to your [repeat match goal] tactic,
   and try it out:
   -1. Whenever a clause [H: Abs E _] is above the line, invert it by [inv H].
             Take note: with just this one clause, how many subgoals remain?
   -2. Whenever [Abs (T _ _ _ _ _) _] is above the line, invert it.
             Take note: with just these two clause, how many subgoals remain?
   -3. Whenever [SearchTree' _ E _] is above the line, invert it.
             Take note after this step and each step: how many subgoals remain?
   -4. Same for [SearchTree' _ (T _ _ _ _ _) _].
   -5. When [Abs match c with Red => _ | Black => _ end _] is below the line,
          [destruct c].
   -6. When [Abs match s with E => _ | T ... => _ end _] is below the line,
          [destruct s].
   -7. Whenever [Abs (T _ _ _ _ _) _] is below the line,
                  prove it by [apply Abs_T].   This won't always work;
         Sometimes the "cts" in the proof goal does not exactly match the form
         of the "cts" required by the [Abs_T] constructor.  But it's all right if
         a clause fails; in that case, the [match goal] will just try the next clause.
          Take note, as usual: how many clauses remain?
   -8.  Whenever [Abs E _] is below the line, solve it by [apply Abs_E].
   -9.  Whenever the current proof goal matches a hypothesis above the line,
          just use it.  That is, just add this clause:
       | |- _ => assumption
   -10.  At this point, if all has gone well, you should have exactly 21 subgoals.
       Each one should be of the form, [  Abs (T ...) (t_update...) ]
       What you want to do is replace (t_update...) with a different "contents"
       that matches the form required by the Abs_T constructor.
       In the first proof goal, do this: [eapply Abs_helper].
       Notice that you have two subgoals.
       The first subgoal you can prove by:
           apply Abs_T. apply Abs_T. apply Abs_E. apply Abs_E.
           apply Abs_T. eassumption. eassumption.
       Step through that, one at a time, to see what it's doing.
       Now, undo those 7 commands, and do this instead:
            repeat econstructor; eassumption.
       That solves the subgoal in exactly the same way.
       Now, wrap this all up, by adding this clause to your [match goal]:
       | |- _ =>  eapply Abs_helper; [repeat econstructor; eassumption | ]
   -11.  You should still have exactly 21 subgoals, each one of the form,
             [ t_update... = t_update... ].  Notice above the line you have some
           assumptions of the form,  [ H: SearchTree' lo _ hi ].  For this equality
         proof, we'll need to know that [lo <= hi].  So, add a clause at the end
        of your [match goal] to apply SearchTree'_le in any such assumption,
        when below the line the proof goal is an equality [ _ = _ ].
   -12.  Still exactly 21 subgoals.  In the first subgoal, try:
          [contents_equivalent_prover].   That should solve the goal.
          Look above, at [Ltac contents_equivalent_prover], to see how it works.
          Now, add a clause to  [match goal] that does this for all the subgoals.

   -Qed! *)
exact FILL_IN_HERE. Qed.

