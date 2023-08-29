section \<open>Ping-Pong Mini-Protocol\<close>

text \<open>
  The theory in this section implements the ping-pong mini-protocol.
\<close>

theory "Ouroboros-Mini_Protocols-Ping_Pong"
  imports
    "Ouroboros-Mini_Protocols"
    "HOL-Library.BNF_Corec"
begin

locale ping_pong =
  fixes no_of_rounds :: nat

subsection \<open>State Machines\<close>

datatype state =
  Idle |
  Busy

datatype message =
  is_ping: Ping |
  is_pong: Pong

primrec agent_in_state' where
  "agent_in_state' Idle = Us" |
  "agent_in_state' Busy = Them"

inductive can_finish_in_state' where
  "can_finish_in_state' Idle"

declare can_finish_in_state'.simps [simp]

primrec next_state' where
  "next_state' Idle m = (partial_case m of Ping \<Rightarrow> Busy)" |
  "next_state' Busy m = (partial_case m of Pong \<Rightarrow> Idle)"

definition client_state_machine where
  [simp]: "client_state_machine = \<lparr>
    initial_state = Idle,
    agent_in_state = agent_in_state',
    can_finish_in_state = can_finish_in_state',
    next_state = next_state'
  \<rparr>"

sublocale ping_pong \<subseteq> protocol_state_machines \<open>client_state_machine\<close> .

subsection \<open>Programs\<close>

corec client_program where
  "client_program n = (case n of
    0 \<Rightarrow>
      \<up> Done;
      \<triangle> () |
    Suc k \<Rightarrow>
      \<up> Cont Ping;
      \<down> M; (partial_case M of
        Cont Pong \<Rightarrow> client_program k
      )
  )"

corec server_program where
  "server_program =
    \<down> M; (partial_case M of
      Done \<Rightarrow>
        \<triangle> () |
      Cont Ping \<Rightarrow>
        \<up> Cont Pong;
        server_program
    )"

sublocale
  ping_pong \<subseteq> protocol_programs \<open>client_possibilities\<close> \<open>client_program no_of_rounds\<close> \<open>server_program\<close>
proof
  show "client_program no_of_rounds \<Colon> Cont client_possibilities"
    by
      (coinduction arbitrary: no_of_rounds rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: client_program.code
        extra_splits: nat.splits or_done.splits message.splits
      )
next
  show "server_program \<Colon> Cont server_possibilities"
    by
      (coinduction rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: server_program.code
        extra_splits: or_done.splits message.splits
      )
qed

subsection \<open>The End\<close>

end
