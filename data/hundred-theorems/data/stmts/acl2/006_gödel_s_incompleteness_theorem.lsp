;; Statement-only formalization of hundred-theorems artifact 006,
;; "Gödel's Incompleteness Theorem": an omega-consistent deductive system
;; extending elementary arithmetic and representing its own axiom predicate
;; has an existentially quantified closed sentence independent of the system.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; The arbitrary system T is an actual (possibly infinite) predicate on
;; formulas, not a finite list or a table of preassigned truth values.

(defstub ht006-system-axiom (system formula) t)

(defun ht006-system-axiom-p (system formula)
  (if (ht006-system-axiom system formula) t nil))

;; Terms and formulas for the source language LNN. Variables are natural
;; numbers; terms use 0, successor, addition, and multiplication, and the
;; sole non-equality relation symbol is less-than.

(mutual-recursion
 (defun ht006-term-p (term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((atom term) (equal term :zero))
    ((equal (car term) :var)
     (and (true-listp term)
          (equal (len term) 2)
          (natp (cadr term))))
    ((equal (car term) :succ)
     (and (true-listp term)
          (equal (len term) 2)
          (ht006-term-p (cadr term))))
    ((or (equal (car term) :plus)
         (equal (car term) :times))
     (and (true-listp term)
          (equal (len term) 3)
          (ht006-term-p (cadr term))
          (ht006-term-p (caddr term))))
    (t nil)))

 (defun ht006-formula-p (formula)
   (declare (xargs :measure (acl2-count formula)))
   (cond
    ((atom formula) nil)
    ((equal (car formula) :equal)
     (and (true-listp formula)
          (equal (len formula) 3)
          (ht006-term-p (cadr formula))
          (ht006-term-p (caddr formula))))
    ((equal (car formula) :less)
     (and (true-listp formula)
          (equal (len formula) 3)
          (ht006-term-p (cadr formula))
          (ht006-term-p (caddr formula))))
    ((equal (car formula) :not)
     (and (true-listp formula)
          (equal (len formula) 2)
          (ht006-formula-p (cadr formula))))
    ((equal (car formula) :implies)
     (and (true-listp formula)
          (equal (len formula) 3)
          (ht006-formula-p (cadr formula))
          (ht006-formula-p (caddr formula))))
    ((equal (car formula) :forall)
     (and (true-listp formula)
          (equal (len formula) 3)
          (natp (cadr formula))
          (ht006-formula-p (caddr formula))))
    (t nil))))

(defun ht006-var (variable)
  (list :var (nfix variable)))

(defun ht006-succ (term)
  (list :succ term))

(defun ht006-plus (left right)
  (list :plus left right))

(defun ht006-times (left right)
  (list :times left right))

(defun ht006-equal (left right)
  (list :equal left right))

(defun ht006-less (left right)
  (list :less left right))

(defun ht006-negate (formula)
  (list :not formula))

(defun ht006-implies (antecedent consequent)
  (list :implies antecedent consequent))

(defun ht006-forall (variable formula)
  (list :forall (nfix variable) formula))

(defun ht006-exists (variable formula)
  (ht006-negate
   (ht006-forall variable (ht006-negate formula))))

(defun ht006-or (left right)
  (ht006-implies (ht006-negate left) right))

(mutual-recursion
 (defun ht006-term-free-variable-p (term variable)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((atom term) nil)
    ((equal (car term) :var)
     (equal (cadr term) variable))
    ((equal (car term) :succ)
     (ht006-term-free-variable-p (cadr term) variable))
    ((or (equal (car term) :plus)
         (equal (car term) :times))
     (or
      (ht006-term-free-variable-p (cadr term) variable)
      (ht006-term-free-variable-p (caddr term) variable)))
    (t nil)))

 (defun ht006-formula-free-variable-p (formula variable)
   (declare (xargs :measure (acl2-count formula)))
   (cond
    ((atom formula) nil)
    ((or (equal (car formula) :equal)
         (equal (car formula) :less))
     (or
      (ht006-term-free-variable-p (cadr formula) variable)
      (ht006-term-free-variable-p (caddr formula) variable)))
    ((equal (car formula) :not)
     (ht006-formula-free-variable-p (cadr formula) variable))
    ((equal (car formula) :implies)
     (or
      (ht006-formula-free-variable-p (cadr formula) variable)
      (ht006-formula-free-variable-p (caddr formula) variable)))
    ((equal (car formula) :forall)
     (and
      (not (equal (cadr formula) variable))
      (ht006-formula-free-variable-p (caddr formula) variable)))
    (t nil))))

;; The theorem-specific substitutions insert closed numerals. The proof
;; checker also admits arbitrary terms, guarded below by the standard
;; "free for the variable" side condition.

(mutual-recursion
 (defun ht006-substitute-term (term variable replacement)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((atom term) term)
    ((equal (car term) :var)
     (if (equal (cadr term) variable) replacement term))
    ((equal (car term) :succ)
     (ht006-succ
      (ht006-substitute-term
       (cadr term) variable replacement)))
    ((equal (car term) :plus)
     (ht006-plus
      (ht006-substitute-term
       (cadr term) variable replacement)
      (ht006-substitute-term
       (caddr term) variable replacement)))
    ((equal (car term) :times)
     (ht006-times
      (ht006-substitute-term
       (cadr term) variable replacement)
      (ht006-substitute-term
       (caddr term) variable replacement)))
    (t term)))

 (defun ht006-substitute-formula (formula variable replacement)
   (declare (xargs :measure (acl2-count formula)))
   (cond
    ((atom formula) formula)
    ((equal (car formula) :equal)
     (ht006-equal
      (ht006-substitute-term
       (cadr formula) variable replacement)
      (ht006-substitute-term
       (caddr formula) variable replacement)))
    ((equal (car formula) :less)
     (ht006-less
      (ht006-substitute-term
       (cadr formula) variable replacement)
      (ht006-substitute-term
       (caddr formula) variable replacement)))
    ((equal (car formula) :not)
     (ht006-negate
      (ht006-substitute-formula
       (cadr formula) variable replacement)))
    ((equal (car formula) :implies)
     (ht006-implies
      (ht006-substitute-formula
       (cadr formula) variable replacement)
      (ht006-substitute-formula
       (caddr formula) variable replacement)))
    ((equal (car formula) :forall)
     (if (equal (cadr formula) variable)
         formula
       (ht006-forall
        (cadr formula)
        (ht006-substitute-formula
         (caddr formula) variable replacement))))
    (t formula))))

(defun ht006-free-for-p (formula variable term)
  (declare (xargs :measure (acl2-count formula)))
  (cond
   ((atom formula) t)
   ((or (equal (car formula) :equal)
        (equal (car formula) :less))
    t)
   ((equal (car formula) :not)
    (ht006-free-for-p (cadr formula) variable term))
   ((equal (car formula) :implies)
    (and
     (ht006-free-for-p (cadr formula) variable term)
     (ht006-free-for-p (caddr formula) variable term)))
   ((equal (car formula) :forall)
    (let ((binder (cadr formula))
          (body (caddr formula)))
      (or
       (equal binder variable)
       (not
        (ht006-formula-free-variable-p
         body variable))
       (and
        (not
         (ht006-term-free-variable-p term binder))
        (ht006-free-for-p body variable term)))))
   (t nil)))

(defun ht006-numeral (number)
  (declare (xargs :measure (nfix number)))
  (if (zp number)
      :zero
    (ht006-succ (ht006-numeral (- number 1)))))

;; Cantor pairing supplies an unbounded Gödel numbering. The reflection of a
;; formula is the numeral for its code, matching the source construction.

(defun ht006-pair (left right)
  (let* ((left (nfix left))
         (right (nfix right))
         (sum (+ left right)))
    (+ right (floor (* sum (+ sum 1)) 2))))

(mutual-recursion
 (defun ht006-term-code (term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((atom term) 0)
    ((equal (car term) :var)
     (ht006-pair 1 (nfix (cadr term))))
    ((equal (car term) :succ)
     (ht006-pair 2 (ht006-term-code (cadr term))))
    ((equal (car term) :plus)
     (ht006-pair
      3
      (ht006-pair
       (ht006-term-code (cadr term))
       (ht006-term-code (caddr term)))))
    ((equal (car term) :times)
     (ht006-pair
      4
      (ht006-pair
       (ht006-term-code (cadr term))
       (ht006-term-code (caddr term)))))
    (t 0)))

 (defun ht006-formula-code (formula)
   (declare (xargs :measure (acl2-count formula)))
   (cond
    ((atom formula) 0)
    ((equal (car formula) :equal)
     (ht006-pair
      1
      (ht006-pair
       (ht006-term-code (cadr formula))
       (ht006-term-code (caddr formula)))))
    ((equal (car formula) :less)
     (ht006-pair
      2
      (ht006-pair
       (ht006-term-code (cadr formula))
       (ht006-term-code (caddr formula)))))
    ((equal (car formula) :not)
     (ht006-pair
      3 (ht006-formula-code (cadr formula))))
    ((equal (car formula) :implies)
     (ht006-pair
      4
      (ht006-pair
       (ht006-formula-code (cadr formula))
       (ht006-formula-code (caddr formula)))))
    ((equal (car formula) :forall)
     (ht006-pair
      5
      (ht006-pair
       (nfix (cadr formula))
       (ht006-formula-code (caddr formula)))))
    (t 0))))

(defun ht006-reflection-term (formula)
  (ht006-numeral (ht006-formula-code formula)))

;; A concrete Hilbert derivation tree gives the genuine SysPrf relation.
;; Leaves are system axioms or first-order logical/equality axiom instances;
;; modus ponens and generalization are the inference rules.

(defun ht006-proof-conclusion (proof)
  (declare (xargs :measure (acl2-count proof)))
  (cond
   ((atom proof) :invalid-proof-conclusion)
   ((and (equal (car proof) :system)
         (true-listp proof)
         (equal (len proof) 2))
    (cadr proof))
   ((and (equal (car proof) :prop-1)
         (true-listp proof)
         (equal (len proof) 3))
    (ht006-implies
     (cadr proof)
     (ht006-implies (caddr proof) (cadr proof))))
   ((and (equal (car proof) :prop-2)
         (true-listp proof)
         (equal (len proof) 4))
    (let ((a (cadr proof))
          (b (caddr proof))
          (c (cadddr proof)))
      (ht006-implies
       (ht006-implies a (ht006-implies b c))
       (ht006-implies
        (ht006-implies a b)
        (ht006-implies a c)))))
   ((and (equal (car proof) :prop-3)
         (true-listp proof)
         (equal (len proof) 3))
    (let ((a (cadr proof))
          (b (caddr proof)))
      (ht006-implies
       (ht006-implies
        (ht006-negate b) (ht006-negate a))
       (ht006-implies a b))))
   ((and (equal (car proof) :forall-elim)
         (true-listp proof)
         (equal (len proof) 4))
    (let ((variable (cadr proof))
          (formula (caddr proof))
          (term (cadddr proof)))
      (ht006-implies
       (ht006-forall variable formula)
       (ht006-substitute-formula
        formula variable term))))
   ((and (equal (car proof) :forall-distribute)
         (true-listp proof)
         (equal (len proof) 4))
    (let ((variable (cadr proof))
          (a (caddr proof))
          (b (cadddr proof)))
      (ht006-implies
       (ht006-forall variable (ht006-implies a b))
       (ht006-implies a (ht006-forall variable b)))))
   ((and (equal (car proof) :equality-reflexive)
         (true-listp proof)
         (equal (len proof) 2))
    (ht006-equal (cadr proof) (cadr proof)))
   ((and (equal (car proof) :equality-substitute)
         (true-listp proof)
         (equal (len proof) 5))
    (let ((variable (cadr proof))
          (left (caddr proof))
          (right (cadddr proof))
          (formula (car (cddddr proof))))
      (ht006-implies
       (ht006-equal left right)
       (ht006-implies
        (ht006-substitute-formula
         formula variable left)
        (ht006-substitute-formula
         formula variable right)))))
   ((and (equal (car proof) :modus-ponens)
         (true-listp proof)
         (equal (len proof) 3))
    (let ((implication
           (ht006-proof-conclusion (cadr proof)))
          (antecedent
           (ht006-proof-conclusion (caddr proof))))
      (if (and
           (consp implication)
           (equal (car implication) :implies)
           (equal (cadr implication) antecedent))
          (caddr implication)
        :invalid-proof-conclusion)))
   ((and (equal (car proof) :generalize)
         (true-listp proof)
         (equal (len proof) 3))
    (ht006-forall
     (cadr proof)
     (ht006-proof-conclusion (caddr proof))))
   (t :invalid-proof-conclusion)))

;; This is the finite hypothesis list carried by the source Prf judgment:
;; AXM contributes one hypothesis, MP concatenates the two finite lists,
;; GEN preserves its premise's list, and logical/equality axioms contribute
;; no hypotheses.

(defun ht006-proof-hypotheses (proof)
  (declare (xargs :measure (acl2-count proof)))
  (cond
   ((atom proof) nil)
   ((equal (car proof) :system)
    (if (and
         (true-listp proof)
         (equal (len proof) 2))
        (list (cadr proof))
      nil))
   ((equal (car proof) :modus-ponens)
    (if (and
         (true-listp proof)
         (equal (len proof) 3))
        (append
         (ht006-proof-hypotheses (cadr proof))
         (ht006-proof-hypotheses (caddr proof)))
      nil))
   ((equal (car proof) :generalize)
    (if (and
         (true-listp proof)
         (equal (len proof) 3))
        (ht006-proof-hypotheses (caddr proof))
      nil))
   (t nil)))

(defun ht006-variable-absent-from-hypotheses-p
    (hypotheses variable)
  (declare (xargs :measure (acl2-count hypotheses)))
  (if (atom hypotheses)
      t
    (and
     (not
      (ht006-formula-free-variable-p
       (car hypotheses) variable))
     (ht006-variable-absent-from-hypotheses-p
      (cdr hypotheses) variable))))

(defun ht006-proof-valid-p (system proof)
  (declare (xargs :measure (acl2-count proof)))
  (cond
   ((atom proof) nil)
   ((equal (car proof) :system)
    (and
     (true-listp proof)
     (equal (len proof) 2)
     (ht006-formula-p (cadr proof))
     (ht006-system-axiom-p system (cadr proof))))
   ((equal (car proof) :prop-1)
    (and
     (true-listp proof)
     (equal (len proof) 3)
     (ht006-formula-p (cadr proof))
     (ht006-formula-p (caddr proof))))
   ((equal (car proof) :prop-2)
    (and
     (true-listp proof)
     (equal (len proof) 4)
     (ht006-formula-p (cadr proof))
     (ht006-formula-p (caddr proof))
     (ht006-formula-p (cadddr proof))))
   ((equal (car proof) :prop-3)
    (and
     (true-listp proof)
     (equal (len proof) 3)
     (ht006-formula-p (cadr proof))
     (ht006-formula-p (caddr proof))))
   ((equal (car proof) :forall-elim)
    (and
     (true-listp proof)
     (equal (len proof) 4)
     (natp (cadr proof))
     (ht006-formula-p (caddr proof))
     (ht006-term-p (cadddr proof))
     (ht006-free-for-p
      (caddr proof)
      (cadr proof)
      (cadddr proof))))
   ((equal (car proof) :forall-distribute)
    (and
     (true-listp proof)
     (equal (len proof) 4)
     (natp (cadr proof))
     (ht006-formula-p (caddr proof))
     (ht006-formula-p (cadddr proof))
     (not
      (ht006-formula-free-variable-p
       (caddr proof) (cadr proof)))))
   ((equal (car proof) :equality-reflexive)
    (and
     (true-listp proof)
     (equal (len proof) 2)
     (ht006-term-p (cadr proof))))
   ((equal (car proof) :equality-substitute)
    (and
     (true-listp proof)
     (equal (len proof) 5)
     (natp (cadr proof))
     (ht006-term-p (caddr proof))
     (ht006-term-p (cadddr proof))
     (ht006-formula-p (car (cddddr proof)))
     (ht006-free-for-p
      (car (cddddr proof))
      (cadr proof)
      (caddr proof))
     (ht006-free-for-p
      (car (cddddr proof))
      (cadr proof)
      (cadddr proof))))
   ((equal (car proof) :modus-ponens)
    (and
     (true-listp proof)
     (equal (len proof) 3)
     (ht006-proof-valid-p system (cadr proof))
     (ht006-proof-valid-p system (caddr proof))
     (ht006-formula-p
      (ht006-proof-conclusion proof))))
   ((equal (car proof) :generalize)
    (and
     (true-listp proof)
     (equal (len proof) 3)
     (natp (cadr proof))
     (ht006-proof-valid-p system (caddr proof))
     (ht006-variable-absent-from-hypotheses-p
      (ht006-proof-hypotheses (caddr proof))
      (cadr proof))
     (ht006-formula-p
      (ht006-proof-conclusion proof))))
   (t nil)))

(defun-sk ht006-sys-prf-p (system formula)
  (exists (proof)
    (and
     (ht006-formula-p formula)
     (ht006-proof-valid-p system proof)
     (equal
      (ht006-proof-conclusion proof)
      formula))))

;; The fixed elementary arithmetic system NN is exactly the source's
;; nine axioms NN1--NN9 in this concrete LNN language.

(defun ht006-nn-axiom-1 ()
  (let ((x (ht006-var 0)))
    (ht006-forall
     0
     (ht006-negate
      (ht006-equal (ht006-succ x) :zero)))))

(defun ht006-nn-axiom-2 ()
  (let ((x (ht006-var 0))
        (y (ht006-var 1)))
    (ht006-forall
     1
     (ht006-forall
      0
      (ht006-implies
       (ht006-equal (ht006-succ x) (ht006-succ y))
       (ht006-equal x y))))))

(defun ht006-nn-axiom-3 ()
  (let ((x (ht006-var 0)))
    (ht006-forall
     0
     (ht006-equal (ht006-plus x :zero) x))))

(defun ht006-nn-axiom-4 ()
  (let ((x (ht006-var 0))
        (y (ht006-var 1)))
    (ht006-forall
     1
     (ht006-forall
      0
      (ht006-equal
       (ht006-plus x (ht006-succ y))
       (ht006-succ (ht006-plus x y)))))))

(defun ht006-nn-axiom-5 ()
  (let ((x (ht006-var 0)))
    (ht006-forall
     0
     (ht006-equal (ht006-times x :zero) :zero))))

(defun ht006-nn-axiom-6 ()
  (let ((x (ht006-var 0))
        (y (ht006-var 1)))
    (ht006-forall
     1
     (ht006-forall
      0
      (ht006-equal
       (ht006-times x (ht006-succ y))
       (ht006-plus (ht006-times x y) x))))))

(defun ht006-nn-axiom-7 ()
  (let ((x (ht006-var 0)))
    (ht006-forall
     0
     (ht006-negate
      (ht006-less x :zero)))))

(defun ht006-nn-axiom-8 ()
  (let ((x (ht006-var 0))
        (y (ht006-var 1)))
    (ht006-forall
     1
     (ht006-forall
      0
      (ht006-implies
       (ht006-less x (ht006-succ y))
       (ht006-or
        (ht006-less x y)
        (ht006-equal x y)))))))

(defun ht006-nn-axiom-9 ()
  (let ((x (ht006-var 0))
        (y (ht006-var 1)))
    (ht006-forall
     1
     (ht006-forall
      0
      (ht006-or
       (ht006-less x y)
       (ht006-or
        (ht006-equal x y)
        (ht006-less y x)))))))

(defun ht006-nn-axiom-p (formula)
  (or
   (equal formula (ht006-nn-axiom-1))
   (equal formula (ht006-nn-axiom-2))
   (equal formula (ht006-nn-axiom-3))
   (equal formula (ht006-nn-axiom-4))
   (equal formula (ht006-nn-axiom-5))
   (equal formula (ht006-nn-axiom-6))
   (equal formula (ht006-nn-axiom-7))
   (equal formula (ht006-nn-axiom-8))
   (equal formula (ht006-nn-axiom-9))))

(defun-sk ht006-extends-nn-p (system)
  (forall (formula)
    (implies
     (ht006-nn-axiom-p formula)
     (ht006-system-axiom-p system formula))))

(defun-sk ht006-only-designated-free-variable-p
    (formula variable)
  (forall (candidate)
    (implies
     (and
      (natp candidate)
      (ht006-formula-free-variable-p
       formula candidate))
     (equal candidate variable))))

(defun-sk ht006-closed-formula-p (formula)
  (forall (variable)
    (implies
     (natp variable)
     (not
      (ht006-formula-free-variable-p
       formula variable)))))

;; These are expressT1 and expressT2 with their source-wide quantification.

(defun-sk ht006-positive-representation-p
    (system representing-formula variable)
  (forall (formula)
    (implies
     (and
      (ht006-formula-p formula)
      (ht006-system-axiom-p system formula))
     (ht006-sys-prf-p
      system
      (ht006-substitute-formula
       representing-formula
       variable
       (ht006-reflection-term formula))))))

(defun-sk ht006-negative-representation-p
    (system representing-formula variable)
  (forall (formula)
    (implies
     (and
      (ht006-formula-p formula)
      (not
       (ht006-system-axiom-p system formula)))
     (ht006-sys-prf-p
      system
      (ht006-negate
       (ht006-substitute-formula
        representing-formula
        variable
        (ht006-reflection-term formula)))))))

;; Omega-consistency excludes a one-variable formula whose every numeral
;; instance is derivable while its existential negation is also derivable.

(defun-sk ht006-all-numeral-instances-provable-p
    (system formula variable)
  (forall (number)
    (implies
     (natp number)
     (ht006-sys-prf-p
      system
      (ht006-substitute-formula
       formula variable (ht006-numeral number))))))

(defun ht006-omega-inconsistency-witness-p
    (system formula variable)
  (and
   (ht006-formula-p formula)
   (natp variable)
   (ht006-only-designated-free-variable-p
    formula variable)
   (ht006-all-numeral-instances-provable-p
    system formula variable)
   (ht006-sys-prf-p
    system
    (ht006-exists
     variable
     (ht006-negate formula)))))

(defun-sk ht006-omega-inconsistent-p (system)
  (exists (formula variable)
    (ht006-omega-inconsistency-witness-p
     system formula variable)))

(defun ht006-omega-consistent-p (system)
  (not (ht006-omega-inconsistent-p system)))

(defun ht006-independent-p (system formula)
  (and
   (ht006-formula-p formula)
   (not (ht006-sys-prf-p system formula))
   (not
    (ht006-sys-prf-p
     system (ht006-negate formula)))))

(defun-sk ht006-closed-independent-formula-exists-p (system)
  (exists (formula)
    (and
     (ht006-formula-p formula)
     (ht006-independent-p system formula)
     (ht006-closed-formula-p formula))))

(defun hundred-theorems-006-goedels-incompleteness-statement
    (system representing-formula variable)
  (implies
   (and
    (ht006-formula-p representing-formula)
    (natp variable)
    (ht006-extends-nn-p system)
    (ht006-only-designated-free-variable-p
     representing-formula variable)
    (ht006-positive-representation-p
     system representing-formula variable)
    (ht006-negative-representation-p
     system representing-formula variable)
    (ht006-omega-consistent-p system))
   (ht006-closed-independent-formula-exists-p
    system)))

(value-triple :itpeval-statement-checked)
:q
