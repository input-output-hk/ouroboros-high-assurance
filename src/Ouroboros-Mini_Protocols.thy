section \<open>Mini-Protocols\<close>

text \<open>
  The theory in this section is about mini-protocols as described in the document \<^emph>\<open>The Shelley
  Networking Protocol\<close>, available at
  \<^url>\<open>https://input-output-hk.github.io/ouroboros-network/pdfs/network-spec/\<close>.
\<close>

theory "Ouroboros-Mini_Protocols"
  imports
    Main
begin

subsection \<open>Parties\<close>

text \<open>
  We introduce values for denoting parties that are not labeled with the absolute terms “client” and
  “server” but the relative terms “us” and “them”. This enables us to sometimes use the same code
  for handling clients and servers, as it depends on the viewpoint who “us” and “them” are.
\<close>

datatype party = Us | Them

primrec other_party :: "party \<Rightarrow> party" where
  "other_party Us = Them" |
  "other_party Them = Us"

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

codatatype 'm possibilities =
  Possibilities (agent: \<open>party\<close>) (can_finish: \<open>bool\<close>) (next_possibilities: \<open>'m \<rightharpoonup> 'm possibilities\<close>)

text \<open>
  Note that besides the additional \<^const>\<open>agent\<close> field, the \<^type>\<open>possibilities\<close> type
  corresponds exactly to the \<open>language\<close> type introduced in Subsection~2.2 of the \<^emph>\<open>corec\<close>
  tutorial.
\<close>

text \<open>
  Possibilities always denote a situation where at least one message will still be transmitted. The
  \<^const>\<open>can_finish\<close> field being \<^const>\<open>True\<close> signals that it is possible for a “done” message
  to be transmitted next.
\<close>

text \<open>
  By swapping the notions of “us” and “them” and thus changing the viewpoint, we obtain the dual of
  given possibilities.
\<close>

primcorec dual_possibilities :: "'m possibilities \<Rightarrow> 'm possibilities" (\<open>_\<^sup>\<bottom>\<close> [1000] 1000) where
  "agent P\<^sup>\<bottom> = other_party (agent P)" |
  "can_finish P\<^sup>\<bottom> = can_finish P" |
  "next_possibilities P\<^sup>\<bottom> = map_option dual_possibilities \<circ> next_possibilities P"

text \<open>
  We introduce a relation that tells what possibilities allow what messages to be transmitted next,
  where messages include the “done” message.
\<close>

primrec permit :: "'m possibilities \<Rightarrow> 'm or_done \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 50) where
  "P \<turnstile> Done \<longleftrightarrow> can_finish P" |
  "P \<turnstile> Cont m \<longleftrightarrow> m \<in> dom (next_possibilities P)"

text \<open>
  Based on this relation, we introduce a function that tells when message transmission will end the
  execution of the protocol and, in situations where it will not, what the possibilities afterwards
  are.
\<close>

definition follow_up :: "'m possibilities \<Rightarrow> 'm or_done \<Rightarrow> 'm possibilities or_done" where
  [simp]: "follow_up P M = map_or_done (the \<circ> next_possibilities P) M" if "P \<turnstile> M"

text \<open>
  The communication patterns that a protocol permits are characterized by the possibilities of the
  client and the server, where the latter can be derived from the former via dualization.
\<close>

locale protocol_possibilities =
  fixes client_possibilities :: "'m possibilities"
begin

definition server_possibilities :: "'m possibilities" where
  [simp]: "server_possibilities = client_possibilities\<^sup>\<bottom>"

end

subsection \<open>State Machines\<close>

text \<open>
  We define state machines as incomplete deterministic automatons that additionally assign agents to
  states.
\<close>

record ('s, 'm) state_machine =
  initial_state :: 's
  agent_in_state :: "'s \<Rightarrow> party"
  can_finish_in_state :: "'s \<Rightarrow> bool"
  next_state :: "'s \<Rightarrow> 'm \<rightharpoonup> 's"

text \<open>
  Note that, analogously to possibilities, a state always denotes a situation where at least one
  message will still be transmitted. The \<^const>\<open>can_finish_in_state\<close> function yielding
  \<^const>\<open>True\<close> signals that it is possible for a “done” message to be transmitted next.
\<close>

text \<open>
  By swapping the notions of “us” and “them” and thus changing the viewpoint, we obtain the dual of
  a given state machine.
\<close>

definition
  dual_state_machine :: "('s, 'm) state_machine \<Rightarrow> ('s, 'm) state_machine"
  ("_\<^sup>\<bottom>" [1000] 1000)
where
  [simp]: "S\<^sup>\<bottom> = S \<lparr>agent_in_state := other_party \<circ> agent_in_state S\<rparr>"

text \<open>
  We define as the meaning of a state machine the possibilities corresponding to it. This means that
  the essence of our state machine semantics is forgetting about states.
\<close>

primcorec state_machine_semantics :: "('s, 'm) state_machine \<Rightarrow> 'm possibilities" (\<open>\<lbrakk>_\<rbrakk>\<close>) where
  "agent \<lbrakk>S\<rbrakk> = agent_in_state S (initial_state S)" |
  "can_finish \<lbrakk>S\<rbrakk> = can_finish_in_state S (initial_state S)" |
  "next_possibilities \<lbrakk>S\<rbrakk> = map_option (\<lambda>s. \<lbrakk>S \<lparr>initial_state := s\<rparr>\<rbrakk>) \<circ> next_state S (initial_state S)"

text \<open>
  The state machine semantics preserves dualization.
\<close>

lemma state_machine_semantics_preserves_dualization:
  fixes S :: "('s, 'm) state_machine"
  shows "\<lbrakk>S\<^sup>\<bottom>\<rbrakk> = \<lbrakk>S\<rbrakk>\<^sup>\<bottom>"
proof (coinduction arbitrary: S)
  case Eq_possibilities
  have "agent \<lbrakk>S\<^sup>\<bottom>\<rbrakk> = agent \<lbrakk>S\<rbrakk>\<^sup>\<bottom>"
    by simp
  moreover
  have "can_finish \<lbrakk>S\<^sup>\<bottom>\<rbrakk> = can_finish \<lbrakk>S\<rbrakk>\<^sup>\<bottom>"
    by simp
  moreover
  have "
    rel_option (\<lambda>P\<^sub>1 P\<^sub>2. \<exists>S' :: ('s, 'm) state_machine. P\<^sub>1 = \<lbrakk>S'\<^sup>\<bottom>\<rbrakk> \<and> P\<^sub>2 = \<lbrakk>S'\<rbrakk>\<^sup>\<bottom>)
      (next_possibilities \<lbrakk>S\<^sup>\<bottom>\<rbrakk> m)
      (next_possibilities \<lbrakk>S\<rbrakk>\<^sup>\<bottom> m)"
    for m
  proof (cases "next_state S (initial_state S) m")
    case None
    then show ?thesis
      by simp
  next
    case (Some s)
    define S' where "S' = S \<lparr>initial_state := s\<rparr>"
    with Some have "next_possibilities \<lbrakk>S\<^sup>\<bottom>\<rbrakk> m = Some \<lbrakk>S'\<^sup>\<bottom>\<rbrakk>" and "next_possibilities \<lbrakk>S\<rbrakk>\<^sup>\<bottom> m = Some \<lbrakk>S'\<rbrakk>\<^sup>\<bottom>"
      by (cases S, simp_all)
    then show ?thesis
      by (auto simp only: option.simps)
  qed
  ultimately show ?case
    by blast
qed

text \<open>
  The possibilities that characterize the communication patterns that a protocol permits can be
  described using state machines. A state machine for the client is sufficient for specifying the
  permitted communication patterns, since the state machine for the server can be derived from it
  via dualization.
\<close>

locale protocol_state_machines =
  fixes client_state_machine :: "('s, 'm) state_machine"
begin

definition server_state_machine :: "('s, 'm) state_machine" where
  [simp]: "server_state_machine = client_state_machine\<^sup>\<bottom>"

definition client_possibilities :: "'m possibilities" where
  [simp]: "client_possibilities = \<lbrakk>client_state_machine\<rbrakk>"

sublocale protocol_possibilities \<open>client_possibilities\<close> .

lemma server_possibilities_from_state_machine:
  shows "server_possibilities = \<lbrakk>server_state_machine\<rbrakk>"
  unfolding server_possibilities_def and server_state_machine_def
  unfolding client_possibilities_def
  using state_machine_semantics_preserves_dualization [symmetric] .

end

subsection \<open>Programs\<close>

text \<open>
  A program implements either the client or the server part of a protocol.
\<close>

codatatype ('M, 'r) program =
  Return \<open>'r\<close> (\<open>\<triangle> _\<close> [56] 55) |
  Send \<open>'M\<close> \<open>('M, 'r) program\<close> (\<open>\<up> _;/ _\<close> [0, 55] 55) |
  Receive \<open>'M \<rightharpoonup> ('M, 'r) program\<close>

syntax
  "_Receive" :: "pttrn \<Rightarrow> ('M, 'r) program \<Rightarrow> ('M, 'r) program"
  (\<open>\<down> _;/ _\<close> [0, 55] 55)
translations
  "\<down> M; \<Pi>" \<rightleftharpoons> "CONST Receive (\<lambda>M. \<Pi>)"
print_translation \<open>
  [Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>Receive\<close> \<^syntax_const>\<open>_Receive\<close>]
\<close>

text \<open>
  Note that we use the type variable~\<^typ>\<open>'M\<close> instead of~\<^typ>\<open>'m\<close> in the definition of
  \<^type>\<open>program\<close> and the syntax declaration for \<^const>\<open>Receive\<close>. We do so to indicate that we
  intend the corresponding type parameter to be instantiated with message types that include “done”
  messages, that is, types of the form \<^typ>\<open>'m or_done\<close>. It might have been better to enforce the
  possibility of sending and receiving “done” messages by defining \<^type>\<open>program\<close> as follows:\<^theory_text>\<open>
    codatatype ('m, 'r) program =
      Return \<open>'r\<close> (\<open>\<triangle> _\<close> [56] 55) |
      Send \<open>'m or_done\<close> \<open>('m, 'r) program\<close> (\<open>\<up> _;/ _\<close> [0, 55] 55) |
      Receive \<open>'m or_done \<rightharpoonup> ('m, 'r) program\<close>
  \<close>
  However, the construction of concrete programs will typically use the \<^emph>\<open>corec\<close> package, which
  apparently cannot cope with this definition at present. The relevant issues are being discussed in
  the mailing list thread that starts at
  \<^url>\<open>https://lists.cam.ac.uk/sympa/arc/cl-isabelle-users/2023-08/msg00000.html\<close>.
\<close>

text \<open>
  We introduce a relation that tells what programs conform to what communication schemes, where a
  communication scheme is either specified by possibilities or is a special “done” scheme, which
  does not permit any further communication.
\<close>

coinductive
  conforms_to :: "('m or_done, 'r) program \<Rightarrow> 'm possibilities or_done \<Rightarrow> bool"
  (infix \<open>\<Colon>\<close> 50)
where
  return_conformance:
    "\<triangle> _ \<Colon> Done" |
  send_conformance:
    "\<up> M; \<Pi> \<Colon> Cont P"
      if "agent P = Us" and "P \<turnstile> M" and "\<Pi> \<Colon> follow_up P M" |
  receive_conformance:
    "\<down> M; \<Xi> M \<Colon> Cont P"
      if "agent P = Them" and "dom \<Xi> = {M. P \<turnstile> M}" and "\<forall>M \<in> dom \<Xi>. the (\<Xi> M) \<Colon> follow_up P M"

text \<open>
  A protocol implementation consists of a client and a server program that conform to the
  possibilities of the protocol.
\<close>

locale protocol_programs =
  protocol_possibilities \<open>client_possibilities\<close> for client_possibilities :: "'m possibilities" +
  fixes client_program :: "('m or_done, 'r\<^sub>c) program"
  fixes server_program :: "('m or_done, 'r\<^sub>s) program"
  assumes client_conformance:
    "client_program \<Colon> Cont client_possibilities"
  assumes server_conformance:
    "server_program \<Colon> Cont server_possibilities"

subsection \<open>Utilities\<close>

text \<open>
  When defining concrete possibilities, state machines, and programs, one often has to construct
  partial functions that perform top-level case distinctions on message arguments. Implementing
  such a partial function in a straightforward manner has the following issues:

    \<^item> For each case where the partial function has a result, the implementation has to wrap this
      result with \<^const>\<open>Some\<close>.

    \<^item> The implementation must contain a default case where it returns \<^const>\<open>None\<close>.

  To avoid these issues, we introduce the \<open>partial_case\<close> construct, which basically works like
  \<open>case\<close> but adds the \<^const>\<open>Some\<close> wrapping and the \<^const>\<open>None\<close> case on the fly.
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
