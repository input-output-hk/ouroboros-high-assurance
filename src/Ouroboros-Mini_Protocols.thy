theory "Ouroboros-Mini_Protocols"
  imports
    Main
begin

primrec sum_swap :: "'a + 'b \<Rightarrow> 'b + 'a" where
  "sum_swap (Inl x) = Inr x" |
  "sum_swap (Inr y) = Inl y"

record ('s\<^sub>1, 'd\<^sub>1, 's\<^sub>2, 'd\<^sub>2) situation =
  state :: "'s\<^sub>1 + 's\<^sub>2"
  data :: "'d\<^sub>1 \<times> 'd\<^sub>2"

definition dual :: "('s\<^sub>1, 'd\<^sub>1, 's\<^sub>2, 'd\<^sub>2) situation \<Rightarrow> ('s\<^sub>2, 'd\<^sub>2, 's\<^sub>1, 'd\<^sub>1) situation" where
  [simp]: "dual situation = \<lparr>state = sum_swap (state situation), data = prod.swap (data situation)\<rparr>"

record ('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p, 'm) steps =
  progression_of_active :: "'s\<^sub>a \<Rightarrow> 'd\<^sub>a \<Rightarrow> ('m \<times> 'd\<^sub>a) option"
  progression_of_passive :: "'m \<Rightarrow> 's\<^sub>a \<Rightarrow> 'd\<^sub>p \<Rightarrow> 'd\<^sub>p"
  progression_of_both :: "'m \<Rightarrow> 's\<^sub>a \<Rightarrow> 's\<^sub>a + 's\<^sub>p"

definition
  step :: "('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p, 'm) steps \<Rightarrow> 's\<^sub>a \<Rightarrow> 'd\<^sub>a \<times> 'd\<^sub>p \<Rightarrow> ('s\<^sub>a, 'd\<^sub>a, 's\<^sub>p, 'd\<^sub>p) situation option"
where
  [simp]: "step \<S> s\<^sub>a D =
    map_option
      (\<lambda>(m, d\<^sub>a').
        \<lparr>
          state = progression_of_both \<S> m s\<^sub>a,
          data = (d\<^sub>a', progression_of_passive \<S> m s\<^sub>a (snd D))
        \<rparr>
      )
      (progression_of_active \<S> s\<^sub>a (fst D))"

record ('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) transitions =
  client_steps :: "('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) steps"
  server_steps :: "('s\<^sub>s, 'd\<^sub>s, 's\<^sub>c, 'd\<^sub>c, 'm) steps"

definition
  transition :: "
    ('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) transitions \<Rightarrow>
    ('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s) situation \<Rightarrow>
    ('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s) situation option"
where
  [simp]: "transition \<T> \<sigma> = (
    case state \<sigma> of
      Inl s\<^sub>c \<Rightarrow> step (client_steps \<T>) s\<^sub>c (data \<sigma>) |
      Inr s\<^sub>s \<Rightarrow> map_option dual (step (server_steps \<T>) s\<^sub>s (prod.swap (data \<sigma>)))
  )"

record ('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) state_machine =
  init :: "('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s) situation"
  transitions :: "('s\<^sub>c, 'd\<^sub>c, 's\<^sub>s, 'd\<^sub>s, 'm) transitions"

end
