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
  fixes client_send_steps :: "'d\<^sub>c \<Rightarrow> ('a \<times> 'd\<^sub>c) option"
  fixes client_receive_steps :: "'b \<Rightarrow> 'd\<^sub>c \<Rightarrow> 'd\<^sub>c"
  fixes initial_server_data :: 'd\<^sub>s
  fixes server_cont_steps :: "'a \<Rightarrow> 'd\<^sub>s \<Rightarrow> 'b \<times> 'd\<^sub>s"

subsection \<open>Parties\<close>

datatype party =
  Client |
  Server

subsection \<open>State Machines\<close>

datatype state =
  Idle |
  Busy

datatype ('a, 'b) message =
  is_req: Req \<open>'a\<close> |
  is_resp: Resp \<open>'b\<close>

primrec agent_in_state' where
  "agent_in_state' Idle = Client" |
  "agent_in_state' Busy = Server"

inductive can_finish_in_state' where
  "can_finish_in_state' Idle"

declare can_finish_in_state'.simps [simp]

primrec next_state' where
  "next_state' Idle m = (partial_case m of Req _ \<Rightarrow> Busy)" |
  "next_state' Busy m = (partial_case m of Resp _ \<Rightarrow> Idle)"

definition state_machine where
  [simp]: "state_machine = \<lparr>
    initial_state = Idle,
    agent_in_state = agent_in_state',
    can_finish_in_state = can_finish_in_state',
    next_state = next_state'
  \<rparr>"

sublocale request_response \<subseteq> protocol_state_machine \<open>state_machine\<close> .

subsection \<open>Programs\<close>

corec client_program where
  "client_program d\<^sub>c \<sigma> \<rho> = (case \<sigma> d\<^sub>c of
    None \<Rightarrow>
      \<up> Done;
      \<bottom> |
    Some (x, d\<^sub>c') \<Rightarrow>
      \<up> Cont (Req x);
      \<down> M; (partial_case M of
        Cont (Resp y) \<Rightarrow> client_program (\<rho> y d\<^sub>c') \<sigma> \<rho>
      )
  )"

corec server_program where
  "server_program d\<^sub>s \<kappa> =
    \<down> M; (partial_case M of
      Done \<Rightarrow>
        \<bottom> |
      Cont (Req x) \<Rightarrow>
        let (y, d\<^sub>s') = \<kappa> x d\<^sub>s in
        \<up> Cont (Resp y);
        server_program d\<^sub>s' \<kappa>
    )"

context request_response
begin

primrec program where
  "program Client = client_program initial_client_data client_send_steps client_receive_steps" |
  "program Server = server_program initial_server_data server_cont_steps"

end

sublocale request_response \<subseteq> protocol_programs \<open>possibilities\<close> \<open>program\<close>
proof
  have "
    client_program initial_client_data client_send_steps client_receive_steps
    \<Colon>\<^bsub>Client\<^esub>
    Cont possibilities"
    by
      (coinduction arbitrary: initial_client_data rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: client_program.code
        extra_splits: option.splits or_done.splits message.splits
      )
  moreover
  have "
    server_program initial_server_data server_cont_steps
    \<Colon>\<^bsub>Server\<^esub>
    Cont possibilities"
    by
      (coinduction arbitrary: initial_server_data rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: server_program.code
        extra_splits: or_done.splits message.splits prod.splits
      )
  ultimately show "program p \<Colon>\<^bsub>p\<^esub> Cont possibilities" for p
    by (cases p) simp_all
qed

subsection \<open>The End\<close>

end
