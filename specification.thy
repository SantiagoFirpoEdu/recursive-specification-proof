theory "specification"
  imports Main
begin

(* Definição de árvore binária *)
datatype 'a tree = Empty | Node "'a tree" 'a "'a tree"

(* Definição da função cat *)
primrec cat :: "'a list ⇒ 'a list ⇒ 'a list" where
  cat_base: "cat [] l = l" |
  cat_induction: "cat (h # t) l = h # (cat t l)"

(* Definição da função size (tamanho) *)
primrec size :: "'a list ⇒ nat" where
  size_base: "size [] = 0" |
  size_induction: "size (h # t) = 1 + size t"

(* Definição da função numnodes (numnodos) *)
primrec numnodes :: "'a tree ⇒ nat" where
  numnodes_base: "numnodes Empty = 0" |
  numnodes_induction: "numnodes (Node L x R) = 1 + numnodes L + numnodes R"

(* Definição da função mirror (espelho) *)
primrec mirror :: "'a tree ⇒ 'a tree" where
  mirror_base: "mirror Empty = Empty" |
  mirror_induction: "mirror (Node L x R) = Node (mirror R) x (mirror L)"

(* Definição da função content (conteudo) *)
primrec content :: "'a tree ⇒ 'a list" where
  content_base: "content Empty = []" |
  content_induction: "content (Node L x R) = x # (cat (content L) (content R))"

(* lemma da prova 1 para ser reusado na prova 2 *)
lemma cat_size: "size (cat L1 L2) = size L1 + size L2"
proof (induct L1)
  case Nil
  show ?case
  proof -
    have "cat [] L2 = L2" by (simp only: cat_base)
    also have "size (cat [] L2) = size L2" by simp
    also have "size [] = 0" by (simp only: size_base)
    also have "0 + size L2 = size L2" by simp
    also have "size [] + size L2 = size L2" by simp
    thus ?thesis by simp
  qed
next
  case (Cons h t)
  assume induction_hypothesis: "size (cat t L2) = size t + size L2"
  show ?case
  proof -
    have "cat (h # t) L2 = h # (cat t L2)" by (simp only: cat_induction)
    
    have "size (cat (h # t) L2) = 1 + size (cat t L2)" by simp
    also have "... = 1 + (size t + size L2)" using induction_hypothesis by simp
    also have "... = size (h # t) + size L2" by simp
    finally show ?thesis by simp
  qed
qed

(* teorema da prova 2 *)
theorem numnodes_equals_size_of_content: "numnodes A = size (content A)"
proof (induct A)
  case Empty
  show ?case
  proof -
    have "numnodes Empty = 0" by (simp only: numnodes_base)
    have "size (content Empty) = 0" by (simp only: size_base content_base)
    thus ?thesis by simp
  qed
next
  case (Node L x R)
  assume induction_hypothesis_left: "numnodes L = size (content L)"
  assume induction_hypothesis_right: "numnodes R = size (content R)"
  
  show ?case
  proof -
    have "numnodes (Node L x R) = 1 + numnodes L + numnodes R" by (simp only: numnodes_induction)
    have "content (Node L x R) = x # cat (content L) (content R)" by (simp only: content_induction)
    have "size (content (Node L x R)) = 1 + size (cat (content L) (content R))" by simp
    have "size (cat (content L) (content R)) = size (content L) + size (content R)" by (simp only: cat_size)
    have numnodos_tamanho: "numnodes (Node L x R) = 1 + size (content L) + size (content R)"
      using induction_hypothesis_left induction_hypothesis_right by simp
    thus ?thesis by (simp add: cat_size)
  qed
qed

end
