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

subsection \<open>Foundations\<close>

text \<open>
  Perhaps surprisingly, there is no function for changing the alternative (left or right) of a sum
  type value. We provide one here.
\<close>

primrec sum_swap :: "'a + 'b \<Rightarrow> 'b + 'a" where
  "sum_swap (Inl x) = Inr x" |
  "sum_swap (Inr y) = Inl y"

subsection \<open>State machines\<close>

text \<open>
  State machines have final states (“done” states), which are special in that no party has agency in
  them and no transitions may originate from them. Because of these special properties, there are
  many situations where we want to deal with non-final states only. To account for that at the type
  level, we work with types of proper, non-final, states and use a wrapper type that just adds a
  single final state whenever we want to include such a state. We could use the \<^type>\<open>option\<close>
  type for this purpose, with \<^const>\<open>None\<close> denoting the final state and \<^term>\<open>Some s\<close> denoting
  the proper state~\<^term>\<open>s\<close>. However, this could quickly lead to confusion with the use of
  \<^type>\<open>option\<close> for maps, which we use in state machine descriptions. Therefore, we introduce a
  dedicated type \<open>successor\<close> that is isomorphic to \<^type>\<open>option\<close>. We use this type not only for
  representing final \<^emph>\<open>states\<close> but also for representing other “final things”.
\<close>

datatype 'a successor = Done | Continuing 'a

text \<open>
  We introduce a type \<open>situation\<close> for describing the situations that pairs of communicating parties
  can be in. At this point, we do not yet assign different roles to the parties, like client and
  server or party with and party without agency, and instead just talk about party~1 and party~2.

  The \<open>situation\<close> type has the following parameters:

    \<^item> \<^typ>\<open>'s\<^sub>1\<close>, for the states where party~1 has agency

    \<^item> \<^typ>\<open>'d\<^sub>1\<close>, for the mutable data (“internal mutable state”) maintained by party~1

    \<^item> \<^typ>\<open>'s\<^sub>2\<close>, for the states where party~2 has agency

    \<^item> \<^typ>\<open>'d\<^sub>2\<close>, for the mutable data (“internal mutable state”) maintained by party~2

  Note that we distinguish between states according to agency at the type level. Whenever we want to
  refer to states without any constraints on agency, we use the sum type \<^typ>\<open>'s\<^sub>1 + 's\<^sub>2\<close>.
\<close>

record ('s\<^sub>1, 'd\<^sub>1, 's\<^sub>2, 'd\<^sub>2) situation =
  state :: "'s\<^sub>1 + 's\<^sub>2"
  data :: "'d\<^sub>1 \<times> 'd\<^sub>2"

text \<open>
  We define the dual of a situation as this situation with the roles of the two parties swapped.
\<close>

definition dual :: "('s\<^sub>1, 'd\<^sub>1, 's\<^sub>2, 'd\<^sub>2) situation \<Rightarrow> ('s\<^sub>2, 'd\<^sub>2, 's\<^sub>1, 'd\<^sub>1) situation" where
  [simp]: "dual situation = \<lparr>state = sum_swap (state situation), data = prod.swap (data situation)\<rparr>"

text \<open>
  We split the description of a state machine’s transitions into two parts according to the parties
  that initiate the transitions. We call the transitions that can be initiated by a certain party
  the steps of this party. The full specification of the transitions of a state machine then
  consists of the client steps and the server steps of this state machine.

  In the following, we first deal with steps before getting to complete transition systems.
  Throughout our discussion of steps, we call the party to which certain steps belong the active
  party and the other party the passive party.
\<close>

text \<open>
  The basis for specifying steps is a type \<open>unchecked_steps\<close>. This type contains values that
  describe steps but has also certain invalid members, which we later exclude by a subtype
  construction.

  The \<open>unchecked_steps\<close> type has the following parameters:

    \<^item> \<^typ>\<open>'s\<^sub>a\<close>, for the states where the active party has agency

    \<^item> \<^typ>\<open>'d\<^sub>a\<close>, for the mutable data maintained by the active party

    \<^item> \<^typ>\<open>'s\<^sub>p\<close>, for the states where the passive party has agency

    \<^item> \<^typ>\<open>'d\<^sub>p\<close>, for the mutable data maintained by the passive party

    \<^item> \<^typ>\<open>'m\<close>, for the proper messages (all messages except the “done” message)

  A value of type \<open>unchecked_steps\<close> is a record that consists of two fields:

    \<^item> The \<open>initiation\<close> field states whether the active party, based on the current state and its own
      mutable data, chooses to finish the execution of the mini-protocol and, if not, what proper
      message it sends to the passive party and to what value it updates its mutable data.

    \<^item> The \<open>completion\<close> field states to what state the system transitions if the active party sends a
      given proper message while the system is in a given state and how the passive party updates
      its mutable data upon receipt of this message. Not every pair of a message and a current state
      has necessarily a follow-up state and a data update assigned to it, because there may be
      messages that will not be sent in certain states and the \<open>completion\<close> field should not be
      required to deal with situations that cannot occur. However, it is possible that the
      \<open>completion\<close> field does not specify what to do with a message that \<^emph>\<open>can\<close> be sent in the
      respective state. It is exactly this case where a value of type \<open>unchecked_steps\<close> is invalid.
      The function \<open>unchecked_steps_are_valid\<close> defined after \<open>unchecked_steps\<close> makes this notion of
      validity precise.
\<close>

record ('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p, 'm) unchecked_steps =
  initiation :: "'s\<^sub>a \<Rightarrow> 'd\<^sub>a \<Rightarrow> ('m \<times> 'd\<^sub>a) successor"
  completion :: "'m \<Rightarrow> 's\<^sub>a \<rightharpoonup> ('s\<^sub>a + 's\<^sub>p) \<times> ('d\<^sub>p \<Rightarrow> 'd\<^sub>p)"

definition unchecked_steps_are_valid :: "('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p, 'm) unchecked_steps \<Rightarrow> bool" where
  [simp]: "unchecked_steps_are_valid \<S> =
    (\<forall>s\<^sub>a d\<^sub>a m d\<^sub>a'. initiation \<S> s\<^sub>a d\<^sub>a = Continuing (m, d\<^sub>a') \<longrightarrow> s\<^sub>a \<in> dom (completion \<S> m))"

text \<open>
  The meaning of a description of steps is a function that tells for a given current state where the
  active party has agency and given current mutable data of the active and the passive party whether
  as the next step the execution of the mini-protocol will be finished and, if not, what the
  follow-up situation of the system will be. The \<open>unchecked_step\<close> function defined below provides
  the meanings of all valid members of \<^type>\<open>unchecked_steps\<close>. We provide no guarantees regarding
  its results for invalid members of \<^type>\<open>unchecked_steps\<close>.
\<close>

definition
  unchecked_step :: "
    ('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p, 'm) unchecked_steps \<Rightarrow>
    's\<^sub>a \<Rightarrow>
    'd\<^sub>a \<times> 'd\<^sub>p \<Rightarrow>
    ('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p) situation successor"
where
  [simp]: "unchecked_step \<S> s\<^sub>a d =
    map_successor
      (\<lambda>(m, d\<^sub>a'). let (s', D) = the (completion \<S> m s\<^sub>a) in \<lparr>state = s', data = (d\<^sub>a', D (snd d))\<rparr>)
      (initiation \<S> s\<^sub>a (fst d))"

text \<open>
  Based on the above developments, we define the type of steps, which contrary to
  \<^type>\<open>unchecked_steps\<close> comes with a validity guarantee.
\<close>

typedef ('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p, 'm) steps =
  "{\<S> :: ('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p, 'm) unchecked_steps. unchecked_steps_are_valid \<S>}"
proof -
  have "unchecked_steps_are_valid \<lparr>initiation = \<lambda>_ _. Done, completion = \<lambda>_ _. None\<rparr>"
    by simp
  then show ?thesis
    by blast
qed

setup_lifting type_definition_steps

text \<open>
  The \<open>step\<close> function defined below provides the semantics of steps. It is the type-safe analog of
  \<^const>\<open>unchecked_step\<close>.
\<close>

lift_definition
  step :: "
    ('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p, 'm) steps \<Rightarrow>
    's\<^sub>a \<Rightarrow>
    'd\<^sub>a \<times> 'd\<^sub>p \<Rightarrow>
    ('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p) situation successor"
  is unchecked_step .

text \<open>
  As mentioned above, the transitions of a state machine are specified as a combination of the
  client steps and the server steps of this state machine. We capture that by the type definition
  below. Note that the type variables used in this type definition use indices \<open>c\<close> and~\<open>s\<close>, which
  stand for “client” and “server”, respectively.
\<close>

record ('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) transitions =
  client_steps :: "('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) steps"
  server_steps :: "('s\<^sub>s, 'd\<^sub>s, 's\<^sub>c, 'd\<^sub>c, 'm) steps"

text \<open>
  The meaning of a description of transitions is a function that tells for a given situation whether
  as the next step the execution of the mini-protocol will be finished and, if not, what the
  follow-up situation of the system will be. The semantics of transitions is provided by the
  \<open>transition\<close> function.
\<close>

definition
  transition :: "
    ('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) transitions \<Rightarrow>
    ('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s) situation \<Rightarrow>
    ('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s) situation successor"
where
  [simp]: "transition \<T> \<sigma> = (
    case state \<sigma> of
      Inl s\<^sub>c \<Rightarrow> step (client_steps \<T>) s\<^sub>c (data \<sigma>) |
      Inr s\<^sub>s \<Rightarrow> map_successor dual (step (server_steps \<T>) s\<^sub>s (prod.swap (data \<sigma>)))
  )"

text \<open>
  Finally, we specify that a state machine consists of an initial situation and state machine
  transitions.
\<close>

record ('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) state_machine =
  initial :: "('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s) situation"
  transitions :: "('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) transitions"

end
