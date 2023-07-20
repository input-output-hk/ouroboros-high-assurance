theory "Ouroboros-Mini_Protocols"
  imports
    Main
begin

primrec sum_swap :: "'a + 'b \<Rightarrow> 'b + 'a" where
  "sum_swap (Inl x) = Inr x" |
  "sum_swap (Inr y) = Inl y"

datatype 'a successor = Done | Continuing 'a

record ('s\<^sub>1, 'd\<^sub>1, 's\<^sub>2, 'd\<^sub>2) situation =
  state :: "'s\<^sub>1 + 's\<^sub>2"
  data :: "'d\<^sub>1 \<times> 'd\<^sub>2"

definition dual :: "('s\<^sub>1, 'd\<^sub>1, 's\<^sub>2, 'd\<^sub>2) situation \<Rightarrow> ('s\<^sub>2, 'd\<^sub>2, 's\<^sub>1, 'd\<^sub>1) situation" where
  [simp]: "dual situation = \<lparr>state = sum_swap (state situation), data = prod.swap (data situation)\<rparr>"

record ('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p, 'm) steps =
  initiation :: "'s\<^sub>a \<Rightarrow> 'd\<^sub>a \<Rightarrow> ('m \<times> 'd\<^sub>a) successor"
  completion :: "'m \<Rightarrow> 's\<^sub>a \<rightharpoonup> ('s\<^sub>a + 's\<^sub>p) \<times> ('d\<^sub>p \<Rightarrow> 'd\<^sub>p)"

definition
  step :: "('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p, 'm) steps \<Rightarrow> 's\<^sub>a \<Rightarrow> 'd\<^sub>a \<times> 'd\<^sub>p \<Rightarrow> ('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p) situation successor"
where
  [simp]: "step \<S> s\<^sub>a d =
    map_successor
      (\<lambda>(m, d\<^sub>a'). let (s', D) = the (completion \<S> m s\<^sub>a) in \<lparr>state = s', data = (d\<^sub>a', D (snd d))\<rparr>)
      (initiation \<S> s\<^sub>a (fst d))"

record ('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) transitions =
  client_steps :: "('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) steps"
  server_steps :: "('s\<^sub>s, 'd\<^sub>s, 's\<^sub>c, 'd\<^sub>c, 'm) steps"

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

record ('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) state_machine =
  init :: "('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s) situation"
  transitions :: "('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) transitions"

end
