section \<open>Ping-Pong Mini-Protocol\<close>

text \<open>
  The theory in this section implements the ping-pong mini-protocol.
\<close>

theory "Ouroboros-Mini_Protocols-Ping_Pong"
  imports
    "Ouroboros-Mini_Protocols"
begin

datatype client_state =
  Idle

record client_data =
  no_of_pings_left :: nat

datatype client_message =
  Ping

datatype server_state =
  Busy

type_alias server_data = unit

datatype server_message =
  Pong

definition initial' where
  [simp]: "initial' n = \<lparr>state = Inl Idle, data = (\<lparr>no_of_pings_left = n\<rparr>, ())\<rparr>"

fun client_initiation where
  "client_initiation Idle \<lparr>no_of_pings_left = 0\<rparr> = Done" |
  "client_initiation Idle \<lparr>no_of_pings_left = Suc k\<rparr> = Continuing (Ping, \<lparr>no_of_pings_left = k\<rparr>)"

fun client_completion where
  "client_completion Ping Idle = Some (Inr Busy, id)"

lift_definition
  client_steps' :: "(client_state, client_data, client_message, server_state, server_data) steps"
  is "\<lparr>initiation = client_initiation, completion = client_completion\<rparr>"
  by (fastforce elim: client_initiation.elims)

fun server_initiation where
  "server_initiation Busy () = Continuing (Pong, ())"

fun server_completion where
  "server_completion Pong Busy = Some (Inr Idle, id)"

lift_definition
  server_steps' :: "(server_state, server_data, server_message, client_state, client_data) steps"
  is "\<lparr>initiation = server_initiation, completion = server_completion\<rparr>"
  by (fastforce elim: server_initiation.elims)

definition transitions' where
  [simp]: "transitions' = \<lparr>client_steps = client_steps', server_steps = server_steps'\<rparr>"

definition state_machine where
  [simp]: "state_machine n = \<lparr>initial = initial' n, transitions = transitions'\<rparr>"

end
