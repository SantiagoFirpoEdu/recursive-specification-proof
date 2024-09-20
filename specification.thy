theory "specification"
  imports Main
begin

(* Definição de árvore *)
datatype 'a tree = Empty | Node "'a tree" 'a "'a tree"

(* Definição da função cat *)
primrec cat :: "'a list ⇒ 'a list ⇒ 'a list" where
  "cat [] l = l" |
  "cat (h # t) l = h # (cat t l)"

(* Definição da função tamanho *)
primrec tamanho :: "'a list ⇒ nat" where
  "tamanho [] = 0" |
  "tamanho (h # t) = 1 + tamanho t"

(* Definição da função numnodos *)
primrec numnodos :: "'a tree ⇒ nat" where
  "numnodos Empty = 0" |
  "numnodos (Node L x R) = 1 + numnodos L + numnodos R"

(* Definição da função conteudo *)
primrec conteudo :: "'a tree ⇒ 'a list" where
  "conteudo Empty = []" |
  "conteudo (Node L x R) = x # (cat (conteudo L) (conteudo R))"

(* Definição da função espelho *)
primrec espelho :: "'a tree ⇒ 'a tree" where
  "espelho Empty = Empty" |
  "espelho (Node L x R) = Node (espelho R) x (espelho L)"

(* lemma da a prova 1 para ser reusado na prova 2 *)
lemma cat_tamanho: "tamanho (cat L1 L2) = tamanho L1 + tamanho L2"
proof (induct L1)
  case Nil
  show ?case
  proof -
    have "tamanho (cat [] L2) = tamanho L2" by simp
    have "tamanho [] + tamanho L2 = tamanho L2" by simp
    thus ?thesis by simp
  qed
next
  case (Cons h t)
  assume induction_hypothesis: "tamanho (cat t L2) = tamanho t + tamanho L2"
  show ?case
  proof -
    have "tamanho (cat (h # t) L2) = 1 + tamanho (cat t L2)" by simp
    also have "... = 1 + (tamanho t + tamanho L2)" using induction_hypothesis by simp
    also have "... = tamanho (h # t) + tamanho L2" by simp
    finally show ?thesis by simp
  qed
qed

(* teorema da prova 2 *)
theorem numnodos_equals_tamanho_de_conteudo: "numnodos A = tamanho (conteudo A)"
proof (induct A)
  case Empty
  show ?case
  proof -
    have "numnodos Empty = 0" by simp
    have "tamanho (conteudo Empty) = 0" by simp
    thus ?thesis by simp
  qed
next
  case (Node L x R)
  assume induction_hypothesis_left: "numnodos L = tamanho (conteudo L)"
  assume induction_hypothesis_right: "numnodos R = tamanho (conteudo R)"
  
  show ?case
  proof -
    have "numnodos (Node L x R) = 1 + numnodos L + numnodos R" by simp
    have "conteudo (Node L x R) = x # cat (conteudo L) (conteudo R)" by simp
    have "tamanho (conteudo (Node L x R)) = 1 + tamanho (cat (conteudo L) (conteudo R))" by simp
    have "tamanho (cat (conteudo L) (conteudo R)) = tamanho (conteudo L) + tamanho (conteudo R)" by (simp only: cat_tamanho)
    have numnodos_tamanho: "numnodos (Node L x R) = 1 + tamanho (conteudo L) + tamanho (conteudo R)"
      using induction_hypothesis_left induction_hypothesis_right by simp
    thus ?thesis by (simp add: cat_tamanho)
  qed
qed

end
