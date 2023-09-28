section \<open>Mini-Protocols\<close>

text \<open>
  The theory in this section is about mini-protocols as described in the document \<^emph>\<open>The Shelley
  Networking Protocol\<close>, available at
  \<^url>\<open>https://input-output-hk.github.io/ouroboros-network/pdfs/network-spec/\<close>.
\<close>

theory "Ouroboros-Mini_Protocols"
  imports
    Main
    "HOL-Eisbach.Eisbach"
begin

subsection \<open>Inclusion of a “Done” Case\<close>

text \<open>
  The original specification of mini-protocols uses “done” states and “done” messages to deal with
  finalization of protocol execution. However, “done” \<^emph>\<open>states\<close> in particular are somewhat irregular
  in that no party has agency in them and no transitions may originate from them. To simplify
  matters, we exclude “done” states and “done” messages by default. Whenever we need to cover them,
  we use a wrapper type that just adds a single value that denotes “done”. We could use the
  \<^type>\<open>option\<close> type for this purpose, with \<^const>\<open>None\<close> denoting “done”. However, this could
  quickly lead to confusion with the use of \<^type>\<open>option\<close> for maps, which we utilize in several
  places in this theory. Therefore, we introduce a dedicated type \<open>or_done\<close> that is isomorphic to
  \<^type>\<open>option\<close>. We use this type not only for “done” states and “done” messages but also for
  representing other “final things”.
\<close>

datatype 'a or_done = is_done: Done | Cont \<open>'a\<close>

text \<open>
  It is generally not according to our style to introduce discriminators, but we need to introduce
  one here (we chose \<^const>\<open>is_done\<close>) to permit corecursive invocations under \<open>case\<close> in
  implementations of concrete mini-protocols. We discourage the explicit use of this discriminator.
\<close>

subsection \<open>Possibilities\<close>

text \<open>
  Before defining the notion of state machine, we introduce the more fundamental notion of
  possibilities. Possibilities fully specify permitted communication patterns, but in contrast to
  state machines they do not make explicit the states the communication can be in. They are somewhat
  reminiscent of Conway’s games as discussed in \<^emph>\<open>On Numbers and Games\<close>.
\<close>

codatatype ('p, 'm) possibilities = Possibilities
  (agent: \<open>'p\<close>)
  (can_finish: \<open>bool\<close>)
  (next_possibilities: \<open>'m \<rightharpoonup> ('p, 'm) possibilities\<close>)

text \<open>
  Note that besides the additional type parameter~\<^typ>\<open>'p\<close> and the additional \<^const>\<open>agent\<close>
  field, the \<^type>\<open>possibilities\<close> type corresponds exactly to the \<open>language\<close> type introduced in
  Subsection~2.2 of the \<^emph>\<open>corec\<close> tutorial.

  Possibilities always denote a situation where at least one message will still be transmitted. The
  \<^const>\<open>can_finish\<close> field being \<^const>\<open>True\<close> signals that it is possible for a “done” message
  to be transmitted next.
\<close>

text \<open>
  We introduce a relation that tells what possibilities allow what messages to be transmitted next,
  where messages include the “done” message.
\<close>

primrec permit :: "('p, 'm) possibilities \<Rightarrow> 'm or_done \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 50) where
  "P \<turnstile> Done \<longleftrightarrow> can_finish P" |
  "P \<turnstile> Cont m \<longleftrightarrow> m \<in> dom (next_possibilities P)"

text \<open>
  Based on this relation, we introduce a function that tells when message transmission will end the
  execution of the protocol and, in situations where it will not, what the possibilities afterwards
  will be.
\<close>

definition follow_up :: "('p, 'm) possibilities \<Rightarrow> 'm or_done \<Rightarrow> ('p, 'm) possibilities or_done" where
  [simp]: "follow_up P M = map_or_done (the \<circ> next_possibilities P) M" if "P \<turnstile> M"

text \<open>
  The communication patterns that a protocol permits are specified by possibilities.
\<close>

locale protocol_possibilities =
  fixes possibilities :: "('p, 'm) possibilities"

subsection \<open>State Machines\<close>

text \<open>
  We define state machines as incomplete deterministic automatons that additionally assign agents to
  states.
\<close>

record ('s, 'p, 'm) state_machine =
  initial_state :: 's
  agent_in_state :: "'s \<Rightarrow> 'p"
  can_finish_in_state :: "'s \<Rightarrow> bool"
  next_state :: "'s \<Rightarrow> 'm \<rightharpoonup> 's"

text \<open>
  Note that, analogously to possibilities, a state always denotes a situation where at least one
  message will still be transmitted. The \<^const>\<open>can_finish_in_state\<close> function yielding
  \<^const>\<open>True\<close> signals that it is possible for a “done” message to be transmitted next.
\<close>

text \<open>
  We define as the meaning of a state machine the possibilities corresponding to it. As a result, we
  obtain a state machine semantics whose essence is forgetting about states.
\<close>

primcorec state_machine_semantics :: "('s, 'p, 'm) state_machine \<Rightarrow> ('p, 'm) possibilities" (\<open>\<lbrakk>_\<rbrakk>\<close>) where
  "agent \<lbrakk>S\<rbrakk> = agent_in_state S (initial_state S)" |
  "can_finish \<lbrakk>S\<rbrakk> = can_finish_in_state S (initial_state S)" |
  "next_possibilities \<lbrakk>S\<rbrakk> = map_option (\<lambda>s. \<lbrakk>S \<lparr>initial_state := s\<rparr>\<rbrakk>) \<circ> next_state S (initial_state S)"

text \<open>
  The possibilities that characterize the communication patterns that a protocol permits can be
  described using a state machine.
\<close>

locale protocol_state_machine =
  fixes state_machine :: "('s, 'p, 'm) state_machine"
begin

definition possibilities :: "('p, 'm) possibilities" where
  [simp]: "possibilities = \<lbrakk>state_machine\<rbrakk>"

sublocale protocol_possibilities \<open>possibilities\<close> .

end

subsection \<open>Programs\<close>

text \<open>
  A program describes the part of the execution of a protocol that is performed by a single party.
\<close>

codatatype 'M program =
  Finish (\<open>\<bottom>\<close>) |
  Yield \<open>'M\<close> \<open>'M program\<close> (\<open>\<up> _;/ _\<close> [0, 55] 55) |
  Await \<open>'M \<rightharpoonup> 'M program\<close>

syntax
  "_Await" :: "pttrn \<Rightarrow> 'M program \<Rightarrow> 'M program"
  (\<open>\<down> _;/ _\<close> [0, 55] 55)
translations
  "\<down> M; \<Pi>" \<rightleftharpoons> "CONST Await (\<lambda>M. \<Pi>)"
print_translation \<open>
  [Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>Await\<close> \<^syntax_const>\<open>_Await\<close>]
\<close>

text \<open>
  Note that we use the type variable~\<^typ>\<open>'M\<close> instead of~\<^typ>\<open>'m\<close> in the definition of
  \<^type>\<open>program\<close> and the syntax declaration for \<^const>\<open>Await\<close>. We do so to indicate that we
  intend the corresponding type parameter to be instantiated with message types that include “done”
  messages, that is, types of the form \<^typ>\<open>'m or_done\<close>. It might have been better to enforce the
  possibility of yielding and awaiting “done” messages by defining \<^type>\<open>program\<close> as follows:\<^theory_text>\<open>
    codatatype 'm program =
      Finish (\<open>\<bottom>\<close>) |
      Yield \<open>'m or_done\<close> \<open>'m program\<close> (\<open>\<up> _;/ _\<close> [0, 55] 55) |
      Await \<open>'m or_done \<rightharpoonup> 'm program\<close>
  \<close>
  However, the construction of concrete programs will typically use the \<^emph>\<open>corec\<close> package, which in
  Isabelle2022 cannot cope with this definition. The relevant issues are being discussed in the
  mailing list thread that starts at
  \<^url>\<open>https://lists.cam.ac.uk/sympa/arc/cl-isabelle-users/2023-08/msg00000.html\<close>. These issues should
  be resolved in Isabelle2023. Once Isabelle2023 is released, we shall improve the definition of the
  \<^type>\<open>program\<close> type accordingly. See
  \<^url>\<open>https://github.com/input-output-hk/ouroboros-high-assurance/issues/59\<close>.
\<close>

text \<open>
  We introduce a relation that tells what it means for a program to conform to a certain
  communication scheme when run by a certain party, where a communication scheme is either specified
  by possibilities or is a special “done” scheme, which does not permit any further communication.
\<close>

coinductive
  conformance :: "'p \<Rightarrow> 'm or_done program \<Rightarrow> ('p, 'm) possibilities or_done \<Rightarrow> bool"
  (\<open>'(\<Colon>\<^bsub>_\<^esub>')\<close>)
and
  conformance_std :: "'m or_done program \<Rightarrow> 'p \<Rightarrow> ('p, 'm) possibilities or_done \<Rightarrow> bool"
  (\<open>(_ \<Colon>\<^bsub>_\<^esub>/ _)\<close> [51, 0, 51] 50)
for
  p :: 'p
where
  "\<Pi> \<Colon>\<^bsub>p\<^esub> \<P> \<equiv> (\<Colon>\<^bsub>p\<^esub>) \<Pi> \<P>" |
  finish_conformance:
    "\<bottom> \<Colon>\<^bsub>p\<^esub> Done" |
  yield_conformance:
    "\<up> M; \<Pi> \<Colon>\<^bsub>p\<^esub> Cont P"
      if "agent P = p" and "P \<turnstile> M" and "\<Pi> \<Colon>\<^bsub>p\<^esub> follow_up P M" |
  await_conformance:
    "\<down> M; \<Xi> M \<Colon>\<^bsub>p\<^esub> Cont P"
      if "agent P \<noteq> p" and "dom \<Xi> = {M. P \<turnstile> M}" and "\<forall>M \<in> dom \<Xi>. the (\<Xi> M) \<Colon>\<^bsub>p\<^esub> follow_up P M"

text \<open>
  A protocol is implemented by assigning programs to parties such that the programs communicate
  according to the possibilities of the protocol.
\<close>

locale protocol_programs = protocol_possibilities +
  fixes program :: "'p \<Rightarrow> 'm or_done program"
  assumes conformance:
    "\<And>p. program p \<Colon>\<^bsub>p\<^esub> Cont possibilities"

subsection \<open>Coinduction Up to Embedding\<close>

text \<open>
  Conformance of programs can be proved by a technique that we call “coinduction up to embedding”.
  This technique is similar to coinduction up to context; the differences are as follows:

    \<^item> With coinduction up to context, there must be exactly one pair of holes into which the terms
      related by the base relation are plugged; with coinduction up to embedding, there can be an
      arbitrary number of such pairs of holes (even infinitely many are allowed).

    \<^item> Coinduction up to context only works with contexts of finite depth; coinduction up to
      embedding also works with infinitely deep term fragments around the terms related by the base
      relation.
\<close>

subsubsection \<open>The Proof Principle\<close>

text \<open>
  We introduce a party-indexed family of endofunctions on relations that captures the “up to
  embedding” notion and a variant of it that excludes the possibility of having just holes with
  nothing around them.
\<close>

coinductive
  up_to_embedding :: "
    'p \<Rightarrow>
    ('m or_done program \<Rightarrow> ('p, 'm) possibilities or_done \<Rightarrow> bool) \<Rightarrow>
    ('m or_done program \<Rightarrow> ('p, 'm) possibilities or_done \<Rightarrow> bool)"
and
  up_to_actual_embedding :: "
    'p \<Rightarrow>
    ('m or_done program \<Rightarrow> ('p, 'm) possibilities or_done \<Rightarrow> bool) \<Rightarrow>
    ('m or_done program \<Rightarrow> ('p, 'm) possibilities or_done \<Rightarrow> bool)"
for
  p :: 'p
and
  R :: "'m or_done program \<Rightarrow> ('p, 'm) possibilities or_done \<Rightarrow> bool"
where
  up_to_no_actual_embedding:
    "up_to_embedding p R \<Pi> \<P>"
      if "R \<Pi> \<P>" |
  up_to_actual_embedding:
    "up_to_embedding p R \<Pi> \<P>"
      if "up_to_actual_embedding p R \<Pi> \<P>" |
  up_to_finish_embedding:
    "up_to_actual_embedding p R \<bottom> Done" |
  up_to_yield_embedding:
    "up_to_actual_embedding p R (\<up> M; \<Pi>) (Cont P)"
      if
        "agent P = p"
      and
        "P \<turnstile> M"
      and
        "up_to_embedding p R \<Pi> (follow_up P M)" |
  up_to_await_embedding:
    "up_to_actual_embedding p R (\<down> M; \<Xi> M) (Cont P)"
      if
        "agent P \<noteq> p"
      and
        "dom \<Xi> = {M. P \<turnstile> M}"
      and
        "\<forall>M \<in> dom \<Xi>. up_to_embedding p R (the (\<Xi> M)) (follow_up P M)"

text \<open>
  Coinduction up to embedding is sound. The following lemma not only states this soundness but also
  serves as a coinduction rule intended to be used with the @{method coinduction} proof method.
\<close>

lemma up_to_embedding_is_sound [case_names bisimulation]:
  assumes "R \<Pi> \<P>" and bisimulation: "\<And>\<Pi> \<P>. R \<Pi> \<P> \<Longrightarrow> up_to_actual_embedding p R \<Pi> \<P>"
  shows "\<Pi> \<Colon>\<^bsub>p\<^esub> \<P>"
proof -
  from \<open>R \<Pi> \<P>\<close> have \<open>up_to_embedding p R \<Pi> \<P>\<close>
    by (rule up_to_no_actual_embedding)
  then show ?thesis
  proof (coinduction arbitrary: \<Pi> \<P>)
    case conformance
    from \<open>up_to_embedding p R \<Pi> \<P>\<close> have "up_to_actual_embedding p R \<Pi> \<P>"
    proof cases
      case up_to_no_actual_embedding
      with bisimulation show ?thesis .
    next
      case up_to_actual_embedding
      then show ?thesis .
    qed
    then show ?case
      by cases simp_all
  qed
qed

text \<open>
  Note that the use of \<^const>\<open>up_to_actual_embedding\<close> in the bisimulation assumption captures two
  things:

    \<^item> Both terms make corresponding steps.

    \<^item> The target terms of these steps are related by \<^term>\<open>up_to_embedding p R\<close>.
\<close>

subsubsection \<open>Automatic Construction of Bisimulation Proofs\<close>

text \<open>
  As indicated above, the initial step of proving program conformance is typically invoking the
  @{method coinduction} method with the \<^theory_text>\<open>up_to_embedding_is_sound\<close> rule. This leaves the user with
  the task of proving a bisimulation up to embedding. Manually proving such a bisimulation property
  can be tedious. We introduce a proof method that performs this task fully automatically in the
  situation where the possibilities are specified as the meaning of a state machine.

  The syntax for invoking said proof method is as follows:
  \<^rail>\<open>'state_machine_bisimulation' \<newline> 'program_expansion:' thm ('extra_splits:' thms)?\<close>
  The \<^theory_text>\<open>program_expansion\<close> parameter specifies the fixed-point equation that defines the program. If
  the specification of the program or the state machine uses \<open>case\<close> or \<open>let\<close> expressions that
  involve pattern matching, the \<open>case\<close> split rules for all types for which pattern matching is
  performed should be passed as the \<^theory_text>\<open>extra_splits\<close> parameter. For a type~\<open>t\<close>, the corresponding
  rules are typically called \<^theory_text>\<open>t.splits\<close>.

  Both the program and the state machine should be specified in a rather straightforward way;
  generating programs or state machines via some sort of advanced meta-programming is likely to
  cause problems. Using self-defined constants to better structure specifications is possible, but
  simplification rules for such constants must be made part of the simpset in order for the prover
  to cope with these constants.

  The \<^theory_text>\<open>state_machine_bisimulation\<close> method also takes the definition of
  \<^const>\<open>protocol_state_machine.possibilities\<close> into account, which frees the user from manually
  initiating the unfolding of this constant when interpreting \<^locale>\<open>protocol_programs\<close> in the
  presence of a \<^locale>\<open>protocol_state_machine\<close> interpretation.
\<close>

method state_machine_bisimulation uses program_expansion extra_splits = (
  subst (2) program_expansion,
  fastforce
    simp add: protocol_state_machine.possibilities_def domIff
    split: extra_splits
    intro: up_to_embedding_up_to_actual_embedding.intros
)

subsection \<open>Case Distinction and Partiality\<close>

text \<open>
  When defining concrete possibilities, state machines, or programs, one often has to construct
  partial functions that perform top-level case distinction on message arguments. Implementing such
  a partial function in a straightforward manner has the following issues:

    \<^item> For each case where the partial function has a result, the implementation has to wrap this
      result with \<^const>\<open>Some\<close>.

    \<^item> The implementation must contain a default case where it returns \<^const>\<open>None\<close>.

  To avoid these issues, we introduce the \<open>partial_case\<close> construct, which allows users to leave out
  the \<^const>\<open>Some\<close> wrapping and the \<^const>\<open>None\<close> case. Under the hood, \<open>partial_case\<close>
  expressions are just turned into \<open>case\<close> expressions via syntax translations, and therefore they
  can be handled like \<open>case\<close> expressions when it comes to proofs.
\<close>

nonterminal partial_case_clauses and partial_case_clause
syntax
  "_partial_case" :: "'a \<Rightarrow> partial_case_clauses \<Rightarrow> 'b option"
  (\<open>(partial'_case _ of/ _)\<close> 10)
syntax
  "_more_partial_case_clauses" :: "partial_case_clause \<Rightarrow> partial_case_clauses \<Rightarrow> partial_case_clauses"
  (\<open>_/ | _\<close>)
syntax
  "_one_partial_case_clause" :: "partial_case_clause \<Rightarrow> partial_case_clauses"
  (\<open>_\<close>)
syntax
  "_partial_case_clause" :: "'a \<Rightarrow> 'b \<Rightarrow> partial_case_clause"
  (\<open>(2_ \<Rightarrow>/ _)\<close> 10)
translations
  "_partial_case x Cs" \<rightharpoonup> "_case_syntax x Cs"
translations
  "_more_partial_case_clauses C Cs" \<rightharpoonup> "_case2 C Cs"
translations
  "_one_partial_case_clause C" \<rightharpoonup> "_case2 C (_case1 _ CONST None)"
translations
  "_partial_case_clause x y" \<rightharpoonup> "_case1 x (CONST Some y)"

subsection \<open>The End\<close>

end
