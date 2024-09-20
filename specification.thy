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

(* lemma da a prova 1 para ser reusado na prova 2 (não sei se podemos fazer assim. A confirmar) *)
lemma cat_tamanho: "tamanho (cat L1 L2) = tamanho L1 + tamanho L2"
proof (induct L1)
  case Nil
  then show ?case by simp
next
  case (Cons h t)
  then show ?case by simp
qed

(* Theorem da prova 2 *)
theorem numnodos_equals_tamanho_de_conteudo: "numnodos A = tamanho (conteudo A)"
proof (induct A)
  case Empty
  then show ?case by simp
next
  case (Node L x R)
  (* Induction hypotheses *)
  assume IH_L: "numnodos L = tamanho (conteudo L)"
  assume IH_R: "numnodos R = tamanho (conteudo R)"
  
  have "numnodos (Node L x R) = 1 + numnodos L + numnodos R" by simp
  moreover have "tamanho (conteudo (Node L x R)) = 1 + tamanho (cat (conteudo L) (conteudo R))" by simp
  moreover have "tamanho (cat (conteudo L) (conteudo R)) = tamanho (conteudo L) + tamanho (conteudo R)"
    using cat_tamanho by simp
  ultimately show ?case using IH_L IH_R by simp
qed

end
