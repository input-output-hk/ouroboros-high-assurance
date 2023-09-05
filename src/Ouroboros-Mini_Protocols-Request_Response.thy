section \<open>Request-Response Mini-Protocol\<close>

text \<open>
  The theory in this section implements the request-response mini-protocol.
\<close>

theory "Ouroboros-Mini_Protocols-Request_Response"
  imports
    "Ouroboros-Mini_Protocols"
    "HOL-Library.BNF_Corec"
begin

locale request_response =
  fixes initial_client_data :: 'd\<^sub>c
  fixes client_send_steps :: "'d\<^sub>c \<Rightarrow> 'r\<^sub>c + 'a \<times> 'd\<^sub>c"
  fixes client_receive_steps :: "'b \<Rightarrow> 'd\<^sub>c \<Rightarrow> 'd\<^sub>c"
  fixes initial_server_data :: 'd\<^sub>s
  fixes server_done_steps :: "'d\<^sub>s \<Rightarrow> 'r\<^sub>s"
  fixes server_cont_steps :: "'a \<Rightarrow> 'd\<^sub>s \<Rightarrow> 'b \<times> 'd\<^sub>s"

subsection \<open>State Machines\<close>

datatype state =
  Idle |
  Busy

datatype ('a, 'b) message =
  is_req: Req \<open>'a\<close> |
  is_resp: Resp \<open>'b\<close>

primrec agent_in_state' where
  "agent_in_state' Idle = Us" |
  "agent_in_state' Busy = Them"

inductive can_finish_in_state' where
  "can_finish_in_state' Idle"

declare can_finish_in_state'.simps [simp]

primrec next_state' where
  "next_state' Idle m = (partial_case m of (Req _) \<Rightarrow> Busy)" |
  "next_state' Busy m = (partial_case m of (Resp _) \<Rightarrow> Idle)"

definition client_state_machine where
  [simp]: "client_state_machine = \<lparr>
    initial_state = Idle,
    agent_in_state = agent_in_state',
    can_finish_in_state = can_finish_in_state',
    next_state = next_state'
  \<rparr>"

sublocale request_response \<subseteq> protocol_state_machines \<open>client_state_machine\<close> .

subsection \<open>Programs\<close>

corec client_program where
  "client_program d\<^sub>c \<sigma> \<rho> = (case \<sigma> d\<^sub>c of
    Inl r\<^sub>c \<Rightarrow>
      \<up> Done;
      \<triangle> r\<^sub>c |
    Inr (x, d\<^sub>c') \<Rightarrow>
      \<up> Cont (Req x);
      \<down> M; (partial_case M of
        Cont (Resp y) \<Rightarrow> client_program (\<rho> y d\<^sub>c') \<sigma> \<rho>
      )
  )"

corec server_program where
  "server_program d\<^sub>s \<delta> \<kappa> =
    \<down> M; (partial_case M of
      Done \<Rightarrow>
        \<triangle> \<delta> d\<^sub>s |
      Cont (Req x) \<Rightarrow>
        let (y, d\<^sub>s') = \<kappa> x d\<^sub>s in
        \<up> Cont (Resp y);
        server_program d\<^sub>s' \<delta> \<kappa>
    )"

sublocale
  request_response
  \<subseteq>
  protocol_programs
    \<open>client_possibilities\<close>
    \<open>client_program initial_client_data client_send_steps client_receive_steps\<close>
    \<open>server_program initial_server_data server_done_steps server_cont_steps\<close>
proof
  show "
    client_program initial_client_data client_send_steps client_receive_steps
    \<Colon>
    Cont client_possibilities"
    by
      (coinduction arbitrary: initial_client_data rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: client_program.code
        extra_splits: sum.splits or_done.splits message.splits
      )
next
  show "
    server_program initial_server_data server_done_steps server_cont_steps
    \<Colon>
    Cont server_possibilities"
    by
      (coinduction arbitrary: initial_server_data rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: server_program.code
        extra_splits: or_done.splits message.splits prod.splits
      )
qed

subsection \<open>The End\<close>

end
