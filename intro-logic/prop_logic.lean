-- Thm 1. P ∧ Q → P
theorem and_left (P Q: Prop) : P ∧ Q → P := by
  intro h
  exact h.left


-- Thm 2. P ∧ Q → Q
theorem and_right (P Q: Prop) : P ∧ Q → Q := by
  intro h
  exact h.right


-- Thm 3.
theorem _and_comm (P Q: Prop) : P ∧ Q → Q ∧ P := by
  intro p_and_q
  exact ⟨(and_right P Q) p_and_q, (and_left P Q) p_and_q⟩


-- Thm 4.
theorem _imp_and_distrib (P Q R : Prop) : (P ∧ Q → R) → (P → Q → R) := by
  intro p_and_q_imp_r
  intro p
  intro q
  have pq: P ∧ Q := ⟨p, q⟩
  exact p_and_q_imp_r pq


-- Thm 5. Modus Ponens
theorem modus_ponens (P Q : Prop) : (P ∧ (P → Q)) → Q := by
  intro p_pimpq
  have p : P := p_pimpq.left
  have pimpq : P → Q := p_pimpq.right
  exact pimpq p


-- Thm 6. Contrapositive of Implication
theorem contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  intro pimpq
  intro nq
  intro p
  have q : Q := pimpq p
  exact nq q -- nq is an implication that ¬q → False. So by nq q steps to False


theorem and_or_distrib (P Q R : Prop) : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro p_q_or_r
  have p : P := p_q_or_r.left
  have q_or_r := p_q_or_r.right
