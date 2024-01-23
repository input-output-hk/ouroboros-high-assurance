(*
  Copyright 2021–2024 Input Output Global Inc.

  Licensed under the Apache License, Version 2.0 (the “License”); you may not use this file except
  in compliance with the License. You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software distributed under the License
  is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
  or implied. See the License for the specific language governing permissions and limitations under
  the License.
*)

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

subsection \<open>Parties\<close>

datatype party =
  Client |
  Server

subsection \<open>State Machine\<close>

datatype state =
  Idle |
  Busy

datatype message =
  is_ping: Ping |
  is_pong: Pong

primrec agent_in_state' where
  "agent_in_state' Idle = Client" |
  "agent_in_state' Busy = Server"

inductive can_finish_in_state' where
  "can_finish_in_state' Idle"

declare can_finish_in_state'.simps [simp]

primrec next_state' where
  "next_state' Idle m = (partial_case m of Ping \<Rightarrow> Busy)" |
  "next_state' Busy m = (partial_case m of Pong \<Rightarrow> Idle)"

definition state_machine where
  [simp]: "state_machine = \<lparr>
    initial_state = Idle,
    agent_in_state = agent_in_state',
    can_finish_in_state = can_finish_in_state',
    next_state = next_state'
  \<rparr>"

sublocale ping_pong \<subseteq> protocol_state_machine \<open>state_machine\<close> .

subsection \<open>Programs\<close>

corec client_program where
  "client_program n = (case n of
    0 \<Rightarrow>
      \<up> Done;
      \<bottom> |
    Suc k \<Rightarrow>
      \<up> Cont Ping;
      \<down> M. (partial_case M of
        Cont Pong \<Rightarrow> client_program k
      )
  )"

corec server_program where
  "server_program =
    \<down> M. (partial_case M of
      Done \<Rightarrow>
        \<bottom> |
      Cont Ping \<Rightarrow>
        \<up> Cont Pong;
        server_program
    )"

context ping_pong
begin

primrec program where
  "program Client = client_program no_of_rounds" |
  "program Server = server_program"

end

sublocale ping_pong \<subseteq> protocol_programs \<open>possibilities\<close> \<open>program\<close>
proof
  have "client_program no_of_rounds \<Colon>\<^bsub>Client\<^esub> Cont possibilities"
    by
      (coinduction arbitrary: no_of_rounds rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: client_program.code
        extra_splits: nat.splits or_done.splits message.splits
      )
  moreover
  have "server_program \<Colon>\<^bsub>Server\<^esub> Cont possibilities"
    by
      (coinduction rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: server_program.code
        extra_splits: or_done.splits message.splits
      )
  ultimately show "program p \<Colon>\<^bsub>p\<^esub> Cont possibilities" for p
    by (cases p) simp_all
qed

subsection \<open>The End\<close>

end
